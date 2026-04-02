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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
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
lean_object* v___y_246_; lean_object* v_fileName_255_; lean_object* v_fileMap_256_; lean_object* v_options_257_; lean_object* v_currRecDepth_258_; lean_object* v_maxRecDepth_259_; lean_object* v_ref_260_; lean_object* v_currNamespace_261_; lean_object* v_openDecls_262_; lean_object* v_initHeartbeats_263_; lean_object* v_maxHeartbeats_264_; lean_object* v_quotContext_265_; lean_object* v_currMacroScope_266_; uint8_t v_diag_267_; lean_object* v_cancelTk_x3f_268_; uint8_t v_suppressElabErrors_269_; lean_object* v_inheritedTraceOptions_270_; lean_object* v___x_276_; uint8_t v___x_277_; 
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
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_nat_dec_eq(v_maxRecDepth_259_, v___x_276_);
if (v___x_277_ == 0)
{
uint8_t v___x_278_; 
v___x_278_ = lean_nat_dec_eq(v_currRecDepth_258_, v_maxRecDepth_259_);
if (v___x_278_ == 0)
{
goto v___jp_271_;
}
else
{
lean_object* v___x_279_; 
lean_dec_ref(v_x_240_);
lean_inc(v_ref_260_);
v___x_279_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_260_);
v___y_246_ = v___x_279_;
goto v___jp_245_;
}
}
else
{
goto v___jp_271_;
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
v___jp_271_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v_currRecDepth_258_, v___x_272_);
lean_inc_ref(v_inheritedTraceOptions_270_);
lean_inc(v_cancelTk_x3f_268_);
lean_inc(v_currMacroScope_266_);
lean_inc(v_quotContext_265_);
lean_inc(v_maxHeartbeats_264_);
lean_inc(v_initHeartbeats_263_);
lean_inc(v_openDecls_262_);
lean_inc(v_currNamespace_261_);
lean_inc(v_ref_260_);
lean_inc(v_maxRecDepth_259_);
lean_inc_ref(v_options_257_);
lean_inc_ref(v_fileMap_256_);
lean_inc_ref(v_fileName_255_);
v___x_274_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_274_, 0, v_fileName_255_);
lean_ctor_set(v___x_274_, 1, v_fileMap_256_);
lean_ctor_set(v___x_274_, 2, v_options_257_);
lean_ctor_set(v___x_274_, 3, v___x_273_);
lean_ctor_set(v___x_274_, 4, v_maxRecDepth_259_);
lean_ctor_set(v___x_274_, 5, v_ref_260_);
lean_ctor_set(v___x_274_, 6, v_currNamespace_261_);
lean_ctor_set(v___x_274_, 7, v_openDecls_262_);
lean_ctor_set(v___x_274_, 8, v_initHeartbeats_263_);
lean_ctor_set(v___x_274_, 9, v_maxHeartbeats_264_);
lean_ctor_set(v___x_274_, 10, v_quotContext_265_);
lean_ctor_set(v___x_274_, 11, v_currMacroScope_266_);
lean_ctor_set(v___x_274_, 12, v_cancelTk_x3f_268_);
lean_ctor_set(v___x_274_, 13, v_inheritedTraceOptions_270_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*14, v_diag_267_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*14 + 1, v_suppressElabErrors_269_);
lean_inc(v___y_243_);
lean_inc(v___y_241_);
v___x_275_ = lean_apply_4(v_x_240_, v___y_241_, v___x_274_, v___y_243_, lean_box(0));
v___y_246_ = v___x_275_;
goto v___jp_245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_286_, lean_object* v_x_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_apply_1(v_x_287_, lean_box(0));
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_293_, lean_object* v_x_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_293_, v_x_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_299_, lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_box(0);
return v___x_301_;
}
else
{
lean_object* v_key_302_; lean_object* v_value_303_; lean_object* v_tail_304_; uint8_t v___x_305_; 
v_key_302_ = lean_ctor_get(v_x_300_, 0);
v_value_303_ = lean_ctor_get(v_x_300_, 1);
v_tail_304_ = lean_ctor_get(v_x_300_, 2);
v___x_305_ = l_Lean_ExprStructEq_beq(v_key_302_, v_a_299_);
if (v___x_305_ == 0)
{
v_x_300_ = v_tail_304_;
goto _start;
}
else
{
lean_object* v___x_307_; 
lean_inc(v_value_303_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v_value_303_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_308_, v_x_309_);
lean_dec(v_x_309_);
lean_dec_ref(v_a_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_buckets_313_; lean_object* v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v_fold_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_buckets_313_ = lean_ctor_get(v_m_311_, 1);
v___x_314_ = lean_array_get_size(v_buckets_313_);
v___x_315_ = l_Lean_ExprStructEq_hash(v_a_312_);
v___x_316_ = 32ULL;
v___x_317_ = lean_uint64_shift_right(v___x_315_, v___x_316_);
v_fold_318_ = lean_uint64_xor(v___x_315_, v___x_317_);
v___x_319_ = 16ULL;
v___x_320_ = lean_uint64_shift_right(v_fold_318_, v___x_319_);
v___x_321_ = lean_uint64_xor(v_fold_318_, v___x_320_);
v___x_322_ = lean_uint64_to_usize(v___x_321_);
v___x_323_ = lean_usize_of_nat(v___x_314_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_sub(v___x_323_, v___x_324_);
v___x_326_ = lean_usize_land(v___x_322_, v___x_325_);
v___x_327_ = lean_array_uget_borrowed(v_buckets_313_, v___x_326_);
v___x_328_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_312_, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_329_, v_a_330_);
lean_dec_ref(v_a_330_);
lean_dec_ref(v_m_329_);
return v_res_331_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_333_; lean_object* v_dummy_334_; 
v___x_333_ = lean_box(0);
v_dummy_334_ = l_Lean_Expr_sort___override(v___x_333_);
return v_dummy_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_335_, lean_object* v_post_336_, size_t v_sz_337_, size_t v_i_338_, lean_object* v_bs_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
uint8_t v___x_344_; 
v___x_344_ = lean_usize_dec_lt(v_i_338_, v_sz_337_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
lean_dec_ref(v_post_336_);
lean_dec_ref(v_pre_335_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v_bs_339_);
return v___x_345_;
}
else
{
lean_object* v_v_346_; lean_object* v___x_347_; 
v_v_346_ = lean_array_uget_borrowed(v_bs_339_, v_i_338_);
lean_inc(v_v_346_);
lean_inc_ref(v_post_336_);
lean_inc_ref(v_pre_335_);
v___x_347_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_335_, v_post_336_, v_v_346_, v___y_340_, v___y_341_, v___y_342_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v_bs_x27_350_; size_t v___x_351_; size_t v___x_352_; lean_object* v___x_353_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref(v___x_347_);
v___x_349_ = lean_unsigned_to_nat(0u);
v_bs_x27_350_ = lean_array_uset(v_bs_339_, v_i_338_, v___x_349_);
v___x_351_ = ((size_t)1ULL);
v___x_352_ = lean_usize_add(v_i_338_, v___x_351_);
v___x_353_ = lean_array_uset(v_bs_x27_350_, v_i_338_, v_a_348_);
v_i_338_ = v___x_352_;
v_bs_339_ = v___x_353_;
goto _start;
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref(v_bs_339_);
lean_dec_ref(v_post_336_);
lean_dec_ref(v_pre_335_);
v_a_355_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_347_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_347_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_363_, lean_object* v_post_364_, lean_object* v_x_365_, lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
if (lean_obj_tag(v_x_365_) == 5)
{
lean_object* v_fn_372_; lean_object* v_arg_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_fn_372_ = lean_ctor_get(v_x_365_, 0);
lean_inc_ref(v_fn_372_);
v_arg_373_ = lean_ctor_get(v_x_365_, 1);
lean_inc_ref(v_arg_373_);
lean_dec_ref(v_x_365_);
v___x_374_ = lean_array_set(v_x_366_, v_x_367_, v_arg_373_);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_sub(v_x_367_, v___x_375_);
lean_dec(v_x_367_);
v_x_365_ = v_fn_372_;
v_x_366_ = v___x_374_;
v_x_367_ = v___x_376_;
goto _start;
}
else
{
lean_object* v___x_378_; 
lean_dec(v_x_367_);
lean_inc_ref(v_post_364_);
lean_inc_ref(v_pre_363_);
v___x_378_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_363_, v_post_364_, v_x_365_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; size_t v_sz_380_; size_t v___x_381_; lean_object* v___x_382_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref(v___x_378_);
v_sz_380_ = lean_array_size(v_x_366_);
v___x_381_ = ((size_t)0ULL);
lean_inc_ref(v_post_364_);
lean_inc_ref(v_pre_363_);
v___x_382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_363_, v_post_364_, v_sz_380_, v___x_381_, v_x_366_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref(v___x_382_);
v___x_384_ = l_Lean_mkAppN(v_a_379_, v_a_383_);
lean_dec(v_a_383_);
v___x_385_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_363_, v_post_364_, v___x_384_, v___y_368_, v___y_369_, v___y_370_);
return v___x_385_;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec(v_a_379_);
lean_dec_ref(v_post_364_);
lean_dec_ref(v_pre_363_);
v_a_386_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_382_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_382_);
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
lean_dec_ref(v_x_366_);
lean_dec_ref(v_post_364_);
lean_dec_ref(v_pre_363_);
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v___x_394_, lean_object* v_pre_395_, lean_object* v_e_396_, lean_object* v_post_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; uint8_t v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; uint8_t v___y_410_; lean_object* v___y_420_; lean_object* v___y_421_; uint8_t v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; uint8_t v___y_425_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; lean_object* v___y_437_; uint8_t v___y_438_; lean_object* v___x_445_; 
v___x_445_ = l_Lean_Core_checkSystem(v___x_394_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; 
lean_dec_ref(v___x_445_);
lean_inc_ref(v_pre_395_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
lean_inc_ref(v_e_396_);
v___x_446_ = lean_apply_4(v_pre_395_, v_e_396_, v___y_399_, v___y_400_, lean_box(0));
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
lean_dec_ref(v_post_397_);
lean_dec_ref(v_e_396_);
lean_dec_ref(v_pre_395_);
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
lean_dec_ref(v_e_396_);
v_e_530_ = lean_ctor_get(v_a_447_, 0);
lean_inc_ref(v_e_530_);
lean_dec_ref(v_a_447_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_e_530_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_533_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref(v___x_531_);
v___x_533_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v_a_532_, v___y_398_, v___y_399_, v___y_400_);
return v___x_533_;
}
else
{
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
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
v___y_452_ = v_e_396_;
goto v___jp_451_;
}
else
{
lean_object* v_val_535_; 
lean_dec_ref(v_e_396_);
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
lean_inc_ref(v_binderType_454_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_457_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_binderType_454_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref(v___x_457_);
lean_inc_ref(v_body_455_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_body_455_, v___y_398_, v___y_399_, v___y_400_);
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
v___y_433_ = v_a_460_;
v___y_434_ = v_a_458_;
v___y_435_ = v_binderName_453_;
v___y_436_ = v_binderInfo_456_;
v___y_437_ = v___y_452_;
v___y_438_ = v___x_463_;
goto v___jp_432_;
}
else
{
size_t v___x_464_; size_t v___x_465_; uint8_t v___x_466_; 
v___x_464_ = lean_ptr_addr(v_body_455_);
v___x_465_ = lean_ptr_addr(v_a_460_);
v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
v___y_433_ = v_a_460_;
v___y_434_ = v_a_458_;
v___y_435_ = v_binderName_453_;
v___y_436_ = v_binderInfo_456_;
v___y_437_ = v___y_452_;
v___y_438_ = v___x_466_;
goto v___jp_432_;
}
}
else
{
lean_dec(v_a_458_);
lean_dec_ref(v___y_452_);
lean_dec(v_binderName_453_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_459_;
}
}
else
{
lean_dec(v_binderName_453_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
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
lean_inc_ref(v_binderType_468_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_471_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_binderType_468_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref(v___x_471_);
lean_inc_ref(v_body_469_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_body_469_, v___y_398_, v___y_399_, v___y_400_);
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
v___y_420_ = v_a_472_;
v___y_421_ = v_a_474_;
v___y_422_ = v_binderInfo_470_;
v___y_423_ = v_binderName_467_;
v___y_424_ = v___y_452_;
v___y_425_ = v___x_477_;
goto v___jp_419_;
}
else
{
size_t v___x_478_; size_t v___x_479_; uint8_t v___x_480_; 
v___x_478_ = lean_ptr_addr(v_body_469_);
v___x_479_ = lean_ptr_addr(v_a_474_);
v___x_480_ = lean_usize_dec_eq(v___x_478_, v___x_479_);
v___y_420_ = v_a_472_;
v___y_421_ = v_a_474_;
v___y_422_ = v_binderInfo_470_;
v___y_423_ = v_binderName_467_;
v___y_424_ = v___y_452_;
v___y_425_ = v___x_480_;
goto v___jp_419_;
}
}
else
{
lean_dec(v_a_472_);
lean_dec_ref(v___y_452_);
lean_dec(v_binderName_467_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_473_;
}
}
else
{
lean_dec(v_binderName_467_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
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
lean_inc_ref(v_type_482_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_486_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_type_482_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref(v___x_486_);
lean_inc_ref(v_value_483_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_value_483_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
lean_inc_ref(v_body_484_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_body_484_, v___y_398_, v___y_399_, v___y_400_);
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
v___y_403_ = v_declName_481_;
v___y_404_ = v_a_487_;
v___y_405_ = v_a_489_;
v___y_406_ = v_body_484_;
v___y_407_ = v_nondep_485_;
v___y_408_ = v_a_491_;
v___y_409_ = v___y_452_;
v___y_410_ = v___x_494_;
goto v___jp_402_;
}
else
{
size_t v___x_495_; size_t v___x_496_; uint8_t v___x_497_; 
v___x_495_ = lean_ptr_addr(v_value_483_);
v___x_496_ = lean_ptr_addr(v_a_489_);
v___x_497_ = lean_usize_dec_eq(v___x_495_, v___x_496_);
v___y_403_ = v_declName_481_;
v___y_404_ = v_a_487_;
v___y_405_ = v_a_489_;
v___y_406_ = v_body_484_;
v___y_407_ = v_nondep_485_;
v___y_408_ = v_a_491_;
v___y_409_ = v___y_452_;
v___y_410_ = v___x_497_;
goto v___jp_402_;
}
}
else
{
lean_dec(v_a_489_);
lean_dec(v_a_487_);
lean_dec_ref(v_body_484_);
lean_dec(v_declName_481_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_490_;
}
}
else
{
lean_dec(v_a_487_);
lean_dec_ref(v_body_484_);
lean_dec_ref(v___y_452_);
lean_dec(v_declName_481_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_488_;
}
}
else
{
lean_dec_ref(v_body_484_);
lean_dec(v_declName_481_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
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
v___x_503_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_395_, v_post_397_, v___y_452_, v___x_500_, v___x_502_, v___y_398_, v___y_399_, v___y_400_);
return v___x_503_;
}
case 10:
{
lean_object* v_data_504_; lean_object* v_expr_505_; lean_object* v___x_506_; 
v_data_504_ = lean_ctor_get(v___y_452_, 0);
v_expr_505_ = lean_ctor_get(v___y_452_, 1);
lean_inc_ref(v_expr_505_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_expr_505_, v___y_398_, v___y_399_, v___y_400_);
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
v___x_512_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_511_, v___y_398_, v___y_399_, v___y_400_);
return v___x_512_;
}
else
{
lean_object* v___x_513_; 
lean_dec(v_a_507_);
v___x_513_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___y_452_, v___y_398_, v___y_399_, v___y_400_);
return v___x_513_;
}
}
else
{
lean_dec_ref(v___y_452_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_506_;
}
}
case 11:
{
lean_object* v_typeName_514_; lean_object* v_idx_515_; lean_object* v_struct_516_; lean_object* v___x_517_; 
v_typeName_514_ = lean_ctor_get(v___y_452_, 0);
v_idx_515_ = lean_ctor_get(v___y_452_, 1);
v_struct_516_ = lean_ctor_get(v___y_452_, 2);
lean_inc_ref(v_struct_516_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_395_);
v___x_517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_395_, v_post_397_, v_struct_516_, v___y_398_, v___y_399_, v___y_400_);
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
v___x_523_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_522_, v___y_398_, v___y_399_, v___y_400_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; 
lean_dec(v_a_518_);
v___x_524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___y_452_, v___y_398_, v___y_399_, v___y_400_);
return v___x_524_;
}
}
else
{
lean_dec_ref(v___y_452_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_395_);
return v___x_517_;
}
}
default: 
{
lean_object* v___x_525_; 
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___y_452_, v___y_398_, v___y_399_, v___y_400_);
return v___x_525_;
}
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec_ref(v_post_397_);
lean_dec_ref(v_e_396_);
lean_dec_ref(v_pre_395_);
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
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_post_397_);
lean_dec_ref(v_e_396_);
lean_dec_ref(v_pre_395_);
v_a_545_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_445_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_445_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
v___jp_402_:
{
if (v___y_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v___y_409_);
lean_dec_ref(v___y_406_);
v___x_411_ = l_Lean_Expr_letE___override(v___y_403_, v___y_404_, v___y_405_, v___y_408_, v___y_407_);
v___x_412_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_411_, v___y_398_, v___y_399_, v___y_400_);
return v___x_412_;
}
else
{
size_t v___x_413_; size_t v___x_414_; uint8_t v___x_415_; 
v___x_413_ = lean_ptr_addr(v___y_406_);
lean_dec_ref(v___y_406_);
v___x_414_ = lean_ptr_addr(v___y_408_);
v___x_415_ = lean_usize_dec_eq(v___x_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec_ref(v___y_409_);
v___x_416_ = l_Lean_Expr_letE___override(v___y_403_, v___y_404_, v___y_405_, v___y_408_, v___y_407_);
v___x_417_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_416_, v___y_398_, v___y_399_, v___y_400_);
return v___x_417_;
}
else
{
lean_object* v___x_418_; 
lean_dec_ref(v___y_408_);
lean_dec_ref(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
v___x_418_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___y_409_, v___y_398_, v___y_399_, v___y_400_);
return v___x_418_;
}
}
}
v___jp_419_:
{
if (v___y_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec_ref(v___y_424_);
v___x_426_ = l_Lean_Expr_lam___override(v___y_423_, v___y_420_, v___y_421_, v___y_422_);
v___x_427_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_426_, v___y_398_, v___y_399_, v___y_400_);
return v___x_427_;
}
else
{
uint8_t v___x_428_; 
v___x_428_ = l_Lean_instBEqBinderInfo_beq(v___y_422_, v___y_422_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref(v___y_424_);
v___x_429_ = l_Lean_Expr_lam___override(v___y_423_, v___y_420_, v___y_421_, v___y_422_);
v___x_430_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_429_, v___y_398_, v___y_399_, v___y_400_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; 
lean_dec(v___y_423_);
lean_dec_ref(v___y_421_);
lean_dec_ref(v___y_420_);
v___x_431_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___y_424_, v___y_398_, v___y_399_, v___y_400_);
return v___x_431_;
}
}
}
v___jp_432_:
{
if (v___y_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref(v___y_437_);
v___x_439_ = l_Lean_Expr_forallE___override(v___y_435_, v___y_434_, v___y_433_, v___y_436_);
v___x_440_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_439_, v___y_398_, v___y_399_, v___y_400_);
return v___x_440_;
}
else
{
uint8_t v___x_441_; 
v___x_441_ = l_Lean_instBEqBinderInfo_beq(v___y_436_, v___y_436_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec_ref(v___y_437_);
v___x_442_ = l_Lean_Expr_forallE___override(v___y_435_, v___y_434_, v___y_433_, v___y_436_);
v___x_443_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___x_442_, v___y_398_, v___y_399_, v___y_400_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; 
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec_ref(v___y_433_);
v___x_444_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_395_, v_post_397_, v___y_437_, v___y_398_, v___y_399_, v___y_400_);
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v___x_553_, lean_object* v_pre_554_, lean_object* v_e_555_, lean_object* v_post_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v___x_553_, v_pre_554_, v_e_555_, v_post_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_562_, lean_object* v_post_563_, lean_object* v_e_564_, lean_object* v_a_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_inc(v_a_565_);
v___x_569_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_569_, 0, lean_box(0));
lean_closure_set(v___x_569_, 1, lean_box(0));
lean_closure_set(v___x_569_, 2, v_a_565_);
v___x_570_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_569_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_602_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_602_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_602_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_602_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_571_, v_e_564_);
lean_dec(v_a_571_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; lean_object* v___f_577_; lean_object* v___x_578_; 
lean_del_object(v___x_573_);
v___x_576_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_564_);
v___f_577_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_577_, 0, v___x_576_);
lean_closure_set(v___f_577_, 1, v_pre_562_);
lean_closure_set(v___f_577_, 2, v_e_564_);
lean_closure_set(v___f_577_, 3, v_post_563_);
v___x_578_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_577_, v_a_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___f_580_; lean_object* v___x_581_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc_n(v_a_579_, 2);
lean_dec_ref(v___x_578_);
lean_inc(v_a_565_);
v___f_580_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_580_, 0, v_a_565_);
lean_closure_set(v___f_580_, 1, v_e_564_);
lean_closure_set(v___f_580_, 2, v_a_579_);
v___x_581_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_580_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; 
v_unused_589_ = lean_ctor_get(v___x_581_, 0);
lean_dec(v_unused_589_);
v___x_583_ = v___x_581_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_dec(v___x_581_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v_a_579_);
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_579_);
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
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec(v_a_579_);
v_a_590_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_581_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_581_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_dec_ref(v_e_564_);
return v___x_578_;
}
}
else
{
lean_object* v_val_598_; lean_object* v___x_600_; 
lean_dec_ref(v_e_564_);
lean_dec_ref(v_post_563_);
lean_dec_ref(v_pre_562_);
v_val_598_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_val_598_);
lean_dec_ref(v___x_575_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v_val_598_);
v___x_600_ = v___x_573_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_val_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref(v_e_564_);
lean_dec_ref(v_post_563_);
lean_dec_ref(v_pre_562_);
v_a_603_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_570_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_570_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_611_, lean_object* v_post_612_, lean_object* v_e_613_, lean_object* v_a_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; 
lean_inc_ref(v_post_612_);
lean_inc(v___y_616_);
lean_inc_ref(v___y_615_);
lean_inc_ref(v_e_613_);
v___x_618_ = lean_apply_4(v_post_612_, v_e_613_, v___y_615_, v___y_616_, lean_box(0));
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_637_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_637_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_637_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_637_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
switch(lean_obj_tag(v_a_619_))
{
case 0:
{
lean_object* v_e_623_; lean_object* v___x_625_; 
lean_dec_ref(v_e_613_);
lean_dec_ref(v_post_612_);
lean_dec_ref(v_pre_611_);
v_e_623_ = lean_ctor_get(v_a_619_, 0);
lean_inc_ref(v_e_623_);
lean_dec_ref(v_a_619_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_e_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_e_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
case 1:
{
lean_object* v_e_627_; lean_object* v___x_628_; 
lean_del_object(v___x_621_);
lean_dec_ref(v_e_613_);
v_e_627_ = lean_ctor_get(v_a_619_, 0);
lean_inc_ref(v_e_627_);
lean_dec_ref(v_a_619_);
v___x_628_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_611_, v_post_612_, v_e_627_, v_a_614_, v___y_615_, v___y_616_);
return v___x_628_;
}
default: 
{
lean_object* v_e_x3f_629_; 
lean_dec_ref(v_post_612_);
lean_dec_ref(v_pre_611_);
v_e_x3f_629_ = lean_ctor_get(v_a_619_, 0);
lean_inc(v_e_x3f_629_);
lean_dec_ref(v_a_619_);
if (lean_obj_tag(v_e_x3f_629_) == 0)
{
lean_object* v___x_631_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_e_613_);
v___x_631_ = v___x_621_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_e_613_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
else
{
lean_object* v_val_633_; lean_object* v___x_635_; 
lean_dec_ref(v_e_613_);
v_val_633_ = lean_ctor_get(v_e_x3f_629_, 0);
lean_inc(v_val_633_);
lean_dec_ref(v_e_x3f_629_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v_val_633_);
v___x_635_ = v___x_621_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_val_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec_ref(v_e_613_);
lean_dec_ref(v_post_612_);
lean_dec_ref(v_pre_611_);
v_a_638_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_618_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_618_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_646_, lean_object* v_post_647_, lean_object* v_e_648_, lean_object* v_a_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_646_, v_post_647_, v_e_648_, v_a_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v_a_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_654_, lean_object* v_post_655_, lean_object* v_sz_656_, lean_object* v_i_657_, lean_object* v_bs_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
size_t v_sz_boxed_663_; size_t v_i_boxed_664_; lean_object* v_res_665_; 
v_sz_boxed_663_ = lean_unbox_usize(v_sz_656_);
lean_dec(v_sz_656_);
v_i_boxed_664_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_res_665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_654_, v_post_655_, v_sz_boxed_663_, v_i_boxed_664_, v_bs_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_666_, lean_object* v_post_667_, lean_object* v_x_668_, lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_666_, v_post_667_, v_x_668_, v_x_669_, v_x_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_676_, lean_object* v_post_677_, lean_object* v_e_678_, lean_object* v_a_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_676_, v_post_677_, v_e_678_, v_a_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v_a_679_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_684_, lean_object* v_x_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_apply_1(v_x_685_, lean_box(0));
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_691_, lean_object* v_x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_691_, v_x_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_696_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_box(0);
v___x_698_ = lean_unsigned_to_nat(16u);
v___x_699_ = lean_mk_array(v___x_698_, v___x_697_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_700_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_704_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_704_, 0, lean_box(0));
lean_closure_set(v___x_704_, 1, lean_box(0));
lean_closure_set(v___x_704_, 2, v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_705_, lean_object* v_pre_706_, lean_object* v_post_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_a_713_; lean_object* v___x_714_; 
v___x_711_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_712_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_711_, v___y_708_, v___y_709_);
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref(v___x_712_);
v___x_714_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_706_, v_post_707_, v_input_705_, v_a_713_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref(v___x_714_);
v___x_716_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_716_, 0, lean_box(0));
lean_closure_set(v___x_716_, 1, lean_box(0));
lean_closure_set(v___x_716_, 2, v_a_713_);
v___x_717_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_716_, v___y_708_, v___y_709_);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_717_, 0);
lean_dec(v_unused_725_);
v___x_719_ = v___x_717_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_dec(v___x_717_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v_a_715_);
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_715_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
lean_dec(v_a_713_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_726_, lean_object* v_pre_727_, lean_object* v_post_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_726_, v_pre_727_, v_post_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___f_739_; lean_object* v___f_740_; lean_object* v___x_741_; 
v___f_739_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_740_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_741_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_735_, v___f_739_, v___f_740_, v_a_736_, v_a_737_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Meta_elimOptParam(v_type_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_747_, lean_object* v_m_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_748_, v_a_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_751_, lean_object* v_m_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_751_, v_m_752_, v_a_753_);
lean_dec_ref(v_a_753_);
lean_dec_ref(v_m_752_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_755_, lean_object* v_ref_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_756_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_761_, lean_object* v_ref_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_761_, v_ref_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_767_, lean_object* v_x_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_768_, v___y_769_, v___y_770_, v___y_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_774_, lean_object* v_x_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_774_, v_x_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_781_, lean_object* v_m_782_, lean_object* v_a_783_, lean_object* v_b_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_782_, v_a_783_, v_b_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_786_, lean_object* v_a_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_787_, v_x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_790_, lean_object* v_a_791_, lean_object* v_x_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_790_, v_a_791_, v_x_792_);
lean_dec(v_x_792_);
lean_dec_ref(v_a_791_);
return v_res_793_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_794_, lean_object* v_a_795_, lean_object* v_x_796_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(v_a_795_, v_x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_798_, lean_object* v_a_799_, lean_object* v_x_800_){
_start:
{
uint8_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_798_, v_a_799_, v_x_800_);
lean_dec(v_x_800_);
lean_dec_ref(v_a_799_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_803_, lean_object* v_data_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_data_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_806_, lean_object* v_a_807_, lean_object* v_b_808_, lean_object* v_x_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_a_807_, v_b_808_, v_x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_811_, lean_object* v_i_812_, lean_object* v_source_813_, lean_object* v_target_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_812_, v_source_813_, v_target_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_816_, lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_817_, v_x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_820_, lean_object* v_as_821_, size_t v_sz_822_, size_t v_i_823_, lean_object* v_b_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_a_831_; uint8_t v___x_835_; 
v___x_835_ = lean_usize_dec_lt(v_i_823_, v_sz_822_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v_b_824_);
return v___x_836_;
}
else
{
lean_object* v_snd_837_; lean_object* v_fst_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_916_; 
v_snd_837_ = lean_ctor_get(v_b_824_, 1);
v_fst_838_ = lean_ctor_get(v_b_824_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v_b_824_);
if (v_isSharedCheck_916_ == 0)
{
v___x_840_ = v_b_824_;
v_isShared_841_ = v_isSharedCheck_916_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_snd_837_);
lean_inc(v_fst_838_);
lean_dec(v_b_824_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_916_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v_array_842_; lean_object* v_start_843_; lean_object* v_stop_844_; uint8_t v___x_845_; 
v_array_842_ = lean_ctor_get(v_snd_837_, 0);
v_start_843_ = lean_ctor_get(v_snd_837_, 1);
v_stop_844_ = lean_ctor_get(v_snd_837_, 2);
v___x_845_ = lean_nat_dec_lt(v_start_843_, v_stop_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_847_; 
if (v_isShared_841_ == 0)
{
v___x_847_ = v___x_840_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_fst_838_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_snd_837_);
v___x_847_ = v_reuseFailAlloc_849_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
else
{
lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_912_; 
lean_inc(v_stop_844_);
lean_inc(v_start_843_);
lean_inc_ref(v_array_842_);
v_isSharedCheck_912_ = !lean_is_exclusive(v_snd_837_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; lean_object* v_unused_914_; lean_object* v_unused_915_; 
v_unused_913_ = lean_ctor_get(v_snd_837_, 2);
lean_dec(v_unused_913_);
v_unused_914_ = lean_ctor_get(v_snd_837_, 1);
lean_dec(v_unused_914_);
v_unused_915_ = lean_ctor_get(v_snd_837_, 0);
lean_dec(v_unused_915_);
v___x_851_ = v_snd_837_;
v_isShared_852_ = v_isSharedCheck_912_;
goto v_resetjp_850_;
}
else
{
lean_dec(v_snd_837_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_912_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_array_uget_borrowed(v_as_821_, v_i_823_);
lean_inc(v___y_828_);
lean_inc_ref(v___y_827_);
lean_inc(v___y_826_);
lean_inc_ref(v___y_825_);
lean_inc(v_a_853_);
v___x_854_ = lean_infer_type(v_a_853_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref(v___x_854_);
v___x_856_ = lean_array_fget(v_array_842_, v_start_843_);
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = lean_nat_add(v_start_843_, v___x_857_);
lean_dec(v_start_843_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_858_);
v___x_860_ = v___x_851_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_array_842_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_stop_844_);
v___x_860_ = v_reuseFailAlloc_903_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
if (v_skipIfPropOrEq_820_ == 0)
{
lean_object* v___x_861_; 
lean_dec(v_a_855_);
lean_inc(v_a_853_);
v___x_861_ = l_Lean_Meta_mkEqHEq(v_a_853_, v___x_856_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref(v___x_861_);
v___x_863_ = lean_array_push(v_fst_838_, v_a_862_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_860_);
lean_ctor_set(v___x_840_, 0, v___x_863_);
v___x_865_ = v___x_840_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___x_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
v_a_831_ = v___x_865_;
goto v___jp_830_;
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec_ref(v___x_860_);
lean_del_object(v___x_840_);
lean_dec(v_fst_838_);
v_a_867_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_861_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_861_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Meta_isProp(v_a_855_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; uint8_t v___x_881_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref(v___x_875_);
v___x_881_ = lean_unbox(v_a_876_);
lean_dec(v_a_876_);
if (v___x_881_ == 0)
{
uint8_t v___x_882_; 
v___x_882_ = lean_expr_eqv(v_a_853_, v___x_856_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
lean_del_object(v___x_840_);
lean_inc(v_a_853_);
v___x_883_ = l_Lean_Meta_mkEqHEq(v_a_853_, v___x_856_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref(v___x_883_);
v___x_885_ = lean_array_push(v_fst_838_, v_a_884_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_860_);
v_a_831_ = v___x_886_;
goto v___jp_830_;
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec_ref(v___x_860_);
lean_dec(v_fst_838_);
v_a_887_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_883_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_883_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
lean_dec(v___x_856_);
goto v___jp_877_;
}
}
else
{
lean_dec(v___x_856_);
goto v___jp_877_;
}
v___jp_877_:
{
lean_object* v___x_879_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_860_);
v___x_879_ = v___x_840_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_fst_838_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_860_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
v_a_831_ = v___x_879_;
goto v___jp_830_;
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v___x_860_);
lean_dec(v___x_856_);
lean_del_object(v___x_840_);
lean_dec(v_fst_838_);
v_a_895_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_875_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_875_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_del_object(v___x_851_);
lean_dec(v_stop_844_);
lean_dec(v_start_843_);
lean_dec_ref(v_array_842_);
lean_del_object(v___x_840_);
lean_dec(v_fst_838_);
v_a_904_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_854_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_854_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
}
}
v___jp_830_:
{
size_t v___x_832_; size_t v___x_833_; 
v___x_832_ = ((size_t)1ULL);
v___x_833_ = lean_usize_add(v_i_823_, v___x_832_);
v_i_823_ = v___x_833_;
v_b_824_ = v_a_831_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_917_, lean_object* v_as_918_, lean_object* v_sz_919_, lean_object* v_i_920_, lean_object* v_b_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_927_; size_t v_sz_boxed_928_; size_t v_i_boxed_929_; lean_object* v_res_930_; 
v_skipIfPropOrEq_boxed_927_ = lean_unbox(v_skipIfPropOrEq_917_);
v_sz_boxed_928_ = lean_unbox_usize(v_sz_919_);
lean_dec(v_sz_919_);
v_i_boxed_929_ = lean_unbox_usize(v_i_920_);
lean_dec(v_i_920_);
v_res_930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_927_, v_as_918_, v_sz_boxed_928_, v_i_boxed_929_, v_b_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec_ref(v_as_918_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_933_, lean_object* v_args2_934_, uint8_t v_skipIfPropOrEq_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; lean_object* v_eqs_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; size_t v_sz_946_; size_t v___x_947_; lean_object* v___x_948_; 
v___x_941_ = lean_unsigned_to_nat(0u);
v_eqs_942_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_943_ = lean_array_get_size(v_args2_934_);
v___x_944_ = l_Array_toSubarray___redArg(v_args2_934_, v___x_941_, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_eqs_942_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v_sz_946_ = lean_array_size(v_args1_933_);
v___x_947_ = ((size_t)0ULL);
v___x_948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_935_, v_args1_933_, v_sz_946_, v___x_947_, v___x_945_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_957_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_957_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_957_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_957_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_fst_953_; lean_object* v___x_955_; 
v_fst_953_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_fst_953_);
lean_dec(v_a_949_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v_fst_953_);
v___x_955_ = v___x_951_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_fst_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_948_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_948_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_966_, lean_object* v_args2_967_, lean_object* v_skipIfPropOrEq_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_974_; lean_object* v_res_975_; 
v_skipIfPropOrEq_boxed_974_ = lean_unbox(v_skipIfPropOrEq_968_);
v_res_975_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_966_, v_args2_967_, v_skipIfPropOrEq_boxed_974_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec_ref(v_args1_966_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_976_, lean_object* v_b_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_983_; 
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
v___x_983_ = lean_apply_6(v_k_976_, v_b_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, lean_box(0));
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_984_, lean_object* v_b_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_984_, v_b_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_992_, uint8_t v_bi_993_, lean_object* v_type_994_, lean_object* v_k_995_, uint8_t v_kind_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___f_1002_; lean_object* v___x_1003_; 
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1002_, 0, v_k_995_);
v___x_1003_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_992_, v_bi_993_, v_type_994_, v___f_1002_, v_kind_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
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
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_a_1012_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1003_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1003_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1020_, lean_object* v_bi_1021_, lean_object* v_type_1022_, lean_object* v_k_1023_, lean_object* v_kind_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
uint8_t v_bi_boxed_1030_; uint8_t v_kind_boxed_1031_; lean_object* v_res_1032_; 
v_bi_boxed_1030_ = lean_unbox(v_bi_1021_);
v_kind_boxed_1031_ = lean_unbox(v_kind_1024_);
v_res_1032_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1020_, v_bi_boxed_1030_, v_type_1022_, v_k_1023_, v_kind_boxed_1031_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1033_, lean_object* v_name_1034_, uint8_t v_bi_1035_, lean_object* v_type_1036_, lean_object* v_k_1037_, uint8_t v_kind_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1034_, v_bi_1035_, v_type_1036_, v_k_1037_, v_kind_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1045_, lean_object* v_name_1046_, lean_object* v_bi_1047_, lean_object* v_type_1048_, lean_object* v_k_1049_, lean_object* v_kind_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
uint8_t v_bi_boxed_1056_; uint8_t v_kind_boxed_1057_; lean_object* v_res_1058_; 
v_bi_boxed_1056_ = lean_unbox(v_bi_1047_);
v_kind_boxed_1057_ = lean_unbox(v_kind_1050_);
v_res_1058_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1045_, v_name_1046_, v_bi_boxed_1056_, v_type_1048_, v_k_1049_, v_kind_boxed_1057_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v_env_1066_; lean_object* v___x_1067_; lean_object* v_mctx_1068_; lean_object* v_lctx_1069_; lean_object* v_options_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1065_ = lean_st_ref_get(v___y_1063_);
v_env_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc_ref(v_env_1066_);
lean_dec(v___x_1065_);
v___x_1067_ = lean_st_ref_get(v___y_1061_);
v_mctx_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc_ref(v_mctx_1068_);
lean_dec(v___x_1067_);
v_lctx_1069_ = lean_ctor_get(v___y_1060_, 2);
v_options_1070_ = lean_ctor_get(v___y_1062_, 2);
lean_inc_ref(v_options_1070_);
lean_inc_ref(v_lctx_1069_);
v___x_1071_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1071_, 0, v_env_1066_);
lean_ctor_set(v___x_1071_, 1, v_mctx_1068_);
lean_ctor_set(v___x_1071_, 2, v_lctx_1069_);
lean_ctor_set(v___x_1071_, 3, v_options_1070_);
v___x_1072_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v_msgData_1059_);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_ref_1087_; lean_object* v___x_1088_; lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1097_; 
v_ref_1087_ = lean_ctor_get(v___y_1084_, 5);
v___x_1088_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_inc(v_ref_1087_);
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_ref_1087_);
lean_ctor_set(v___x_1093_, 1, v_a_1089_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 1);
lean_ctor_set(v___x_1091_, 0, v___x_1093_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1105_, lean_object* v_body_1106_, lean_object* v_args2_1107_, lean_object* v_args2New_1108_, lean_object* v_ctorVal_1109_, lean_object* v_useEq_1110_, lean_object* v_args1_1111_, lean_object* v_resultType_1112_, lean_object* v_k_1113_, lean_object* v_arg2_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v_useEq_boxed_1120_; lean_object* v_res_1121_; 
v_useEq_boxed_1120_ = lean_unbox(v_useEq_1110_);
v_res_1121_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1105_, v_body_1106_, v_args2_1107_, v_args2New_1108_, v_ctorVal_1109_, v_useEq_boxed_1120_, v_args1_1111_, v_resultType_1112_, v_k_1113_, v_arg2_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec_ref(v_body_1106_);
lean_dec(v_i_1105_);
return v_res_1121_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1124_ = l_Lean_stringToMessageData(v___x_1123_);
return v___x_1124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1127_ = l_Lean_stringToMessageData(v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1128_, uint8_t v_useEq_1129_, lean_object* v_args1_1130_, lean_object* v_resultType_1131_, lean_object* v_k_1132_, lean_object* v_i_1133_, lean_object* v_type_1134_, lean_object* v_args2_1135_, lean_object* v_args2New_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_array_get_size(v_args1_1130_);
v___x_1143_ = lean_nat_dec_lt(v_i_1133_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
lean_dec_ref(v_type_1134_);
lean_dec(v_i_1133_);
lean_dec_ref(v_resultType_1131_);
lean_dec_ref(v_args1_1130_);
lean_dec_ref(v_ctorVal_1128_);
lean_inc(v_a_1140_);
lean_inc_ref(v_a_1139_);
lean_inc(v_a_1138_);
lean_inc_ref(v_a_1137_);
v___x_1144_ = lean_apply_7(v_k_1132_, v_args2_1135_, v_args2New_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, lean_box(0));
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; 
lean_inc(v_a_1140_);
lean_inc_ref(v_a_1139_);
lean_inc(v_a_1138_);
lean_inc_ref(v_a_1137_);
v___x_1145_ = lean_whnf(v_type_1134_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref(v___x_1145_);
if (lean_obj_tag(v_a_1146_) == 7)
{
lean_object* v_binderName_1147_; lean_object* v_binderType_1148_; lean_object* v_body_1149_; lean_object* v_lctx_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v_binderName_1147_ = lean_ctor_get(v_a_1146_, 0);
lean_inc(v_binderName_1147_);
v_binderType_1148_ = lean_ctor_get(v_a_1146_, 1);
lean_inc_ref(v_binderType_1148_);
v_body_1149_ = lean_ctor_get(v_a_1146_, 2);
lean_inc_ref(v_body_1149_);
lean_dec_ref(v_a_1146_);
v_lctx_1150_ = lean_ctor_get(v_a_1137_, 2);
v___x_1151_ = lean_array_fget_borrowed(v_args1_1130_, v_i_1133_);
lean_inc(v___x_1151_);
lean_inc_ref(v_lctx_1150_);
v___x_1152_ = l_Lean_Meta_occursOrInType(v_lctx_1150_, v___x_1151_, v_resultType_1131_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___f_1154_; uint8_t v___y_1156_; 
v___x_1153_ = lean_box(v_useEq_1129_);
v___f_1154_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1154_, 0, v_i_1133_);
lean_closure_set(v___f_1154_, 1, v_body_1149_);
lean_closure_set(v___f_1154_, 2, v_args2_1135_);
lean_closure_set(v___f_1154_, 3, v_args2New_1136_);
lean_closure_set(v___f_1154_, 4, v_ctorVal_1128_);
lean_closure_set(v___f_1154_, 5, v___x_1153_);
lean_closure_set(v___f_1154_, 6, v_args1_1130_);
lean_closure_set(v___f_1154_, 7, v_resultType_1131_);
lean_closure_set(v___f_1154_, 8, v_k_1132_);
if (v_useEq_1129_ == 0)
{
uint8_t v___x_1159_; 
v___x_1159_ = 1;
v___y_1156_ = v___x_1159_;
goto v___jp_1155_;
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = 0;
v___y_1156_ = v___x_1160_;
goto v___jp_1155_;
}
v___jp_1155_:
{
uint8_t v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = 0;
v___x_1158_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1147_, v___y_1156_, v_binderType_1148_, v___f_1154_, v___x_1157_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
return v___x_1158_;
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec_ref(v_binderType_1148_);
lean_dec(v_binderName_1147_);
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_nat_add(v_i_1133_, v___x_1161_);
lean_dec(v_i_1133_);
v___x_1163_ = lean_expr_instantiate1(v_body_1149_, v___x_1151_);
lean_dec_ref(v_body_1149_);
lean_inc(v___x_1151_);
v___x_1164_ = lean_array_push(v_args2_1135_, v___x_1151_);
v_i_1133_ = v___x_1162_;
v_type_1134_ = v___x_1163_;
v_args2_1135_ = v___x_1164_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1166_; lean_object* v_name_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec(v_a_1146_);
lean_dec_ref(v_args2New_1136_);
lean_dec_ref(v_args2_1135_);
lean_dec(v_i_1133_);
lean_dec_ref(v_k_1132_);
lean_dec_ref(v_resultType_1131_);
lean_dec_ref(v_args1_1130_);
v_toConstantVal_1166_ = lean_ctor_get(v_ctorVal_1128_, 0);
lean_inc_ref(v_toConstantVal_1166_);
lean_dec_ref(v_ctorVal_1128_);
v_name_1167_ = lean_ctor_get(v_toConstantVal_1166_, 0);
lean_inc(v_name_1167_);
lean_dec_ref(v_toConstantVal_1166_);
v___x_1168_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1169_ = l_Lean_MessageData_ofName(v_name_1167_);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1172_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
return v___x_1173_;
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v_args2New_1136_);
lean_dec_ref(v_args2_1135_);
lean_dec(v_i_1133_);
lean_dec_ref(v_k_1132_);
lean_dec_ref(v_resultType_1131_);
lean_dec_ref(v_args1_1130_);
lean_dec_ref(v_ctorVal_1128_);
v_a_1174_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1145_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1145_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1182_, lean_object* v_body_1183_, lean_object* v_args2_1184_, lean_object* v_args2New_1185_, lean_object* v_ctorVal_1186_, uint8_t v_useEq_1187_, lean_object* v_args1_1188_, lean_object* v_resultType_1189_, lean_object* v_k_1190_, lean_object* v_arg2_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_nat_add(v_i_1182_, v___x_1197_);
v___x_1199_ = lean_expr_instantiate1(v_body_1183_, v_arg2_1191_);
lean_inc_ref(v_arg2_1191_);
v___x_1200_ = lean_array_push(v_args2_1184_, v_arg2_1191_);
v___x_1201_ = lean_array_push(v_args2New_1185_, v_arg2_1191_);
v___x_1202_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1186_, v_useEq_1187_, v_args1_1188_, v_resultType_1189_, v_k_1190_, v___x_1198_, v___x_1199_, v___x_1200_, v___x_1201_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1203_, lean_object* v_useEq_1204_, lean_object* v_args1_1205_, lean_object* v_resultType_1206_, lean_object* v_k_1207_, lean_object* v_i_1208_, lean_object* v_type_1209_, lean_object* v_args2_1210_, lean_object* v_args2New_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
uint8_t v_useEq_boxed_1217_; lean_object* v_res_1218_; 
v_useEq_boxed_1217_ = lean_unbox(v_useEq_1204_);
v_res_1218_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1203_, v_useEq_boxed_1217_, v_args1_1205_, v_resultType_1206_, v_k_1207_, v_i_1208_, v_type_1209_, v_args2_1210_, v_args2New_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1219_, lean_object* v_msg_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1227_, lean_object* v_msg_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1227_, v_msg_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1235_, lean_object* v_h__1_1236_, lean_object* v_h__2_1237_){
_start:
{
if (lean_obj_tag(v_____x_1235_) == 7)
{
lean_object* v_binderName_1238_; lean_object* v_binderType_1239_; lean_object* v_body_1240_; uint8_t v_binderInfo_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec(v_h__2_1237_);
v_binderName_1238_ = lean_ctor_get(v_____x_1235_, 0);
lean_inc(v_binderName_1238_);
v_binderType_1239_ = lean_ctor_get(v_____x_1235_, 1);
lean_inc_ref(v_binderType_1239_);
v_body_1240_ = lean_ctor_get(v_____x_1235_, 2);
lean_inc_ref(v_body_1240_);
v_binderInfo_1241_ = lean_ctor_get_uint8(v_____x_1235_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1235_);
v___x_1242_ = lean_box(v_binderInfo_1241_);
v___x_1243_ = lean_apply_4(v_h__1_1236_, v_binderName_1238_, v_binderType_1239_, v_body_1240_, v___x_1242_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; 
lean_dec(v_h__1_1236_);
v___x_1244_ = lean_apply_2(v_h__2_1237_, v_____x_1235_, lean_box(0));
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1245_, lean_object* v_____x_1246_, lean_object* v_h__1_1247_, lean_object* v_h__2_1248_){
_start:
{
if (lean_obj_tag(v_____x_1246_) == 7)
{
lean_object* v_binderName_1249_; lean_object* v_binderType_1250_; lean_object* v_body_1251_; uint8_t v_binderInfo_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec(v_h__2_1248_);
v_binderName_1249_ = lean_ctor_get(v_____x_1246_, 0);
lean_inc(v_binderName_1249_);
v_binderType_1250_ = lean_ctor_get(v_____x_1246_, 1);
lean_inc_ref(v_binderType_1250_);
v_body_1251_ = lean_ctor_get(v_____x_1246_, 2);
lean_inc_ref(v_body_1251_);
v_binderInfo_1252_ = lean_ctor_get_uint8(v_____x_1246_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1246_);
v___x_1253_ = lean_box(v_binderInfo_1252_);
v___x_1254_ = lean_apply_4(v_h__1_1247_, v_binderName_1249_, v_binderType_1250_, v_body_1251_, v___x_1253_);
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; 
lean_dec(v_h__1_1247_);
v___x_1255_ = lean_apply_2(v_h__2_1248_, v_____x_1246_, lean_box(0));
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1256_, lean_object* v_b_1257_, lean_object* v_c_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
lean_inc(v___y_1262_);
lean_inc_ref(v___y_1261_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
v___x_1264_ = lean_apply_7(v_k_1256_, v_b_1257_, v_c_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, lean_box(0));
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1265_, lean_object* v_b_1266_, lean_object* v_c_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1265_, v_b_1266_, v_c_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1274_, lean_object* v_k_1275_, uint8_t v_cleanupAnnotations_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___f_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___f_1282_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1282_, 0, v_k_1275_);
v___x_1283_ = 0;
v___x_1284_ = lean_box(0);
v___x_1285_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1283_, v___x_1284_, v_type_1274_, v___f_1282_, v_cleanupAnnotations_1276_, v___x_1283_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_a_1294_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1285_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1285_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1302_, lean_object* v_k_1303_, lean_object* v_cleanupAnnotations_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1310_; lean_object* v_res_1311_; 
v_cleanupAnnotations_boxed_1310_ = lean_unbox(v_cleanupAnnotations_1304_);
v_res_1311_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1302_, v_k_1303_, v_cleanupAnnotations_boxed_1310_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1312_, lean_object* v_type_1313_, lean_object* v_k_1314_, uint8_t v_cleanupAnnotations_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1313_, v_k_1314_, v_cleanupAnnotations_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1322_, lean_object* v_type_1323_, lean_object* v_k_1324_, lean_object* v_cleanupAnnotations_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1331_; lean_object* v_res_1332_; 
v_cleanupAnnotations_boxed_1331_ = lean_unbox(v_cleanupAnnotations_1325_);
v_res_1332_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1322_, v_type_1323_, v_k_1324_, v_cleanupAnnotations_boxed_1331_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1333_, lean_object* v_maxFVars_x3f_1334_, lean_object* v_k_1335_, uint8_t v_cleanupAnnotations_1336_, uint8_t v_whnfType_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___f_1343_; lean_object* v___x_1344_; 
v___f_1343_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1343_, 0, v_k_1335_);
v___x_1344_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1333_, v_maxFVars_x3f_1334_, v___f_1343_, v_cleanupAnnotations_1336_, v_whnfType_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_a_1353_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1344_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1344_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1361_, lean_object* v_maxFVars_x3f_1362_, lean_object* v_k_1363_, lean_object* v_cleanupAnnotations_1364_, lean_object* v_whnfType_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1371_; uint8_t v_whnfType_boxed_1372_; lean_object* v_res_1373_; 
v_cleanupAnnotations_boxed_1371_ = lean_unbox(v_cleanupAnnotations_1364_);
v_whnfType_boxed_1372_ = lean_unbox(v_whnfType_1365_);
v_res_1373_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1361_, v_maxFVars_x3f_1362_, v_k_1363_, v_cleanupAnnotations_boxed_1371_, v_whnfType_boxed_1372_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1374_, lean_object* v_type_1375_, lean_object* v_maxFVars_x3f_1376_, lean_object* v_k_1377_, uint8_t v_cleanupAnnotations_1378_, uint8_t v_whnfType_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1375_, v_maxFVars_x3f_1376_, v_k_1377_, v_cleanupAnnotations_1378_, v_whnfType_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1386_, lean_object* v_type_1387_, lean_object* v_maxFVars_x3f_1388_, lean_object* v_k_1389_, lean_object* v_cleanupAnnotations_1390_, lean_object* v_whnfType_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1397_; uint8_t v_whnfType_boxed_1398_; lean_object* v_res_1399_; 
v_cleanupAnnotations_boxed_1397_ = lean_unbox(v_cleanupAnnotations_1390_);
v_whnfType_boxed_1398_ = lean_unbox(v_whnfType_1391_);
v_res_1399_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1386_, v_type_1387_, v_maxFVars_x3f_1388_, v_k_1389_, v_cleanupAnnotations_boxed_1397_, v_whnfType_boxed_1398_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1400_, lean_object* v_us_1401_, lean_object* v_params_1402_, lean_object* v_args1_1403_, uint8_t v_useEq_1404_, lean_object* v_args2_1405_, lean_object* v_args2New_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1412_ = l_Lean_mkConst(v_name_1400_, v_us_1401_);
v___x_1413_ = l_Lean_mkAppN(v___x_1412_, v_params_1402_);
lean_inc_ref(v___x_1413_);
v___x_1414_ = l_Lean_mkAppN(v___x_1413_, v_args1_1403_);
v___x_1415_ = l_Lean_mkAppN(v___x_1413_, v_args2_1405_);
v___x_1416_ = l_Lean_Meta_mkEq(v___x_1414_, v___x_1415_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; uint8_t v___x_1418_; lean_object* v_result_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___x_1465_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref(v___x_1416_);
v___x_1418_ = 1;
v___x_1465_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1403_, v_args2_1405_, v___x_1418_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1497_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1497_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1497_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; 
v___x_1470_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1466_);
if (lean_obj_tag(v___x_1470_) == 1)
{
lean_del_object(v___x_1468_);
if (v_useEq_1404_ == 0)
{
lean_object* v_val_1471_; lean_object* v___x_1472_; 
v_val_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_val_1471_);
lean_dec_ref(v___x_1470_);
v___x_1472_ = l_Lean_mkArrow(v_a_1417_, v_val_1471_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref(v___x_1472_);
v_result_1420_ = v_a_1473_;
v___y_1421_ = v___y_1407_;
v___y_1422_ = v___y_1408_;
v___y_1423_ = v___y_1409_;
v___y_1424_ = v___y_1410_;
goto v___jp_1419_;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_a_1474_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1472_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1472_);
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
else
{
lean_object* v_val_1482_; lean_object* v___x_1483_; 
v_val_1482_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_val_1482_);
lean_dec_ref(v___x_1470_);
v___x_1483_ = l_Lean_Meta_mkEq(v_a_1417_, v_val_1482_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v_result_1420_ = v_a_1484_;
v___y_1421_ = v___y_1407_;
v___y_1422_ = v___y_1408_;
v___y_1423_ = v___y_1409_;
v___y_1424_ = v___y_1410_;
goto v___jp_1419_;
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
v_a_1485_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1483_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1483_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
lean_dec(v___x_1470_);
lean_dec(v_a_1417_);
v___x_1493_ = lean_box(0);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1493_);
v___x_1495_ = v___x_1468_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_a_1417_);
v_a_1498_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1465_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1465_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
v___jp_1419_:
{
uint8_t v___x_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = 0;
v___x_1426_ = 1;
v___x_1427_ = l_Lean_Meta_mkForallFVars(v_args2New_1406_, v_result_1420_, v___x_1425_, v___x_1418_, v___x_1418_, v___x_1426_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1429_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___x_1427_);
v___x_1429_ = l_Lean_Meta_mkForallFVars(v_args1_1403_, v_a_1428_, v___x_1425_, v___x_1418_, v___x_1418_, v___x_1426_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = l_Lean_Meta_mkForallFVars(v_params_1402_, v_a_1430_, v___x_1425_, v___x_1418_, v___x_1418_, v___x_1426_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1440_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1432_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_a_1441_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1431_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1431_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
v_a_1449_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1429_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1429_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v_a_1457_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1427_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1427_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec_ref(v_args2_1405_);
v_a_1506_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1416_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1416_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1514_, lean_object* v_us_1515_, lean_object* v_params_1516_, lean_object* v_args1_1517_, lean_object* v_useEq_1518_, lean_object* v_args2_1519_, lean_object* v_args2New_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
uint8_t v_useEq_boxed_1526_; lean_object* v_res_1527_; 
v_useEq_boxed_1526_ = lean_unbox(v_useEq_1518_);
v_res_1527_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1514_, v_us_1515_, v_params_1516_, v_args1_1517_, v_useEq_boxed_1526_, v_args2_1519_, v_args2New_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec_ref(v_args2New_1520_);
lean_dec_ref(v_args1_1517_);
lean_dec_ref(v_params_1516_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1528_, size_t v_i_1529_, lean_object* v_bs_1530_){
_start:
{
uint8_t v___x_1531_; 
v___x_1531_ = lean_usize_dec_lt(v_i_1529_, v_sz_1528_);
if (v___x_1531_ == 0)
{
return v_bs_1530_;
}
else
{
lean_object* v_v_1532_; lean_object* v___x_1533_; lean_object* v_bs_x27_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; size_t v___x_1539_; size_t v___x_1540_; lean_object* v___x_1541_; 
v_v_1532_ = lean_array_uget(v_bs_1530_, v_i_1529_);
v___x_1533_ = lean_unsigned_to_nat(0u);
v_bs_x27_1534_ = lean_array_uset(v_bs_1530_, v_i_1529_, v___x_1533_);
v___x_1535_ = l_Lean_Expr_fvarId_x21(v_v_1532_);
lean_dec(v_v_1532_);
v___x_1536_ = 1;
v___x_1537_ = lean_box(v___x_1536_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1535_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = ((size_t)1ULL);
v___x_1540_ = lean_usize_add(v_i_1529_, v___x_1539_);
v___x_1541_ = lean_array_uset(v_bs_x27_1534_, v_i_1529_, v___x_1538_);
v_i_1529_ = v___x_1540_;
v_bs_1530_ = v___x_1541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1543_, lean_object* v_i_1544_, lean_object* v_bs_1545_){
_start:
{
size_t v_sz_boxed_1546_; size_t v_i_boxed_1547_; lean_object* v_res_1548_; 
v_sz_boxed_1546_ = lean_unbox_usize(v_sz_1543_);
lean_dec(v_sz_1543_);
v_i_boxed_1547_ = lean_unbox_usize(v_i_1544_);
lean_dec(v_i_1544_);
v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1546_, v_i_boxed_1547_, v_bs_1545_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1549_, lean_object* v_k_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1549_, v_k_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
v_a_1565_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1556_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1556_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1573_, lean_object* v_k_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1573_, v_k_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec_ref(v_bs_1573_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1581_, lean_object* v_k_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
size_t v_sz_1588_; size_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_sz_1588_ = lean_array_size(v_bs_1581_);
v___x_1589_ = ((size_t)0ULL);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1588_, v___x_1589_, v_bs_1581_);
v___x_1591_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1590_, v_k_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec_ref(v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1592_, lean_object* v_k_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1592_, v_k_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1600_, lean_object* v_us_1601_, lean_object* v_params_1602_, uint8_t v_useEq_1603_, lean_object* v_ctorVal_1604_, lean_object* v_type_1605_, lean_object* v_args1_1606_, lean_object* v_resultType_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___x_1613_; lean_object* v___f_1614_; 
v___x_1613_ = lean_box(v_useEq_1603_);
lean_inc_ref(v_args1_1606_);
lean_inc_ref(v_params_1602_);
v___f_1614_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1614_, 0, v_name_1600_);
lean_closure_set(v___f_1614_, 1, v_us_1601_);
lean_closure_set(v___f_1614_, 2, v_params_1602_);
lean_closure_set(v___f_1614_, 3, v_args1_1606_);
lean_closure_set(v___f_1614_, 4, v___x_1613_);
if (v_useEq_1603_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1615_ = l_Array_append___redArg(v_params_1602_, v_args1_1606_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1618_ = lean_box(v_useEq_1603_);
v___x_1619_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1619_, 0, v_ctorVal_1604_);
lean_closure_set(v___x_1619_, 1, v___x_1618_);
lean_closure_set(v___x_1619_, 2, v_args1_1606_);
lean_closure_set(v___x_1619_, 3, v_resultType_1607_);
lean_closure_set(v___x_1619_, 4, v___f_1614_);
lean_closure_set(v___x_1619_, 5, v___x_1616_);
lean_closure_set(v___x_1619_, 6, v_type_1605_);
lean_closure_set(v___x_1619_, 7, v___x_1617_);
lean_closure_set(v___x_1619_, 8, v___x_1617_);
v___x_1620_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1615_, v___x_1619_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1620_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
lean_dec_ref(v_params_1602_);
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1623_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1604_, v_useEq_1603_, v_args1_1606_, v_resultType_1607_, v___f_1614_, v___x_1621_, v_type_1605_, v___x_1622_, v___x_1622_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1624_, lean_object* v_us_1625_, lean_object* v_params_1626_, lean_object* v_useEq_1627_, lean_object* v_ctorVal_1628_, lean_object* v_type_1629_, lean_object* v_args1_1630_, lean_object* v_resultType_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
uint8_t v_useEq_boxed_1637_; lean_object* v_res_1638_; 
v_useEq_boxed_1637_ = lean_unbox(v_useEq_1627_);
v_res_1638_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1624_, v_us_1625_, v_params_1626_, v_useEq_boxed_1637_, v_ctorVal_1628_, v_type_1629_, v_args1_1630_, v_resultType_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1639_, lean_object* v_us_1640_, uint8_t v_useEq_1641_, lean_object* v_ctorVal_1642_, lean_object* v_params_1643_, lean_object* v_type_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; lean_object* v___f_1651_; uint8_t v___x_1652_; lean_object* v___x_1653_; 
v___x_1650_ = lean_box(v_useEq_1641_);
lean_inc_ref(v_type_1644_);
v___f_1651_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1651_, 0, v_name_1639_);
lean_closure_set(v___f_1651_, 1, v_us_1640_);
lean_closure_set(v___f_1651_, 2, v_params_1643_);
lean_closure_set(v___f_1651_, 3, v___x_1650_);
lean_closure_set(v___f_1651_, 4, v_ctorVal_1642_);
lean_closure_set(v___f_1651_, 5, v_type_1644_);
v___x_1652_ = 0;
v___x_1653_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1644_, v___f_1651_, v___x_1652_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1654_, lean_object* v_us_1655_, lean_object* v_useEq_1656_, lean_object* v_ctorVal_1657_, lean_object* v_params_1658_, lean_object* v_type_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v_useEq_boxed_1665_; lean_object* v_res_1666_; 
v_useEq_boxed_1665_ = lean_unbox(v_useEq_1656_);
v_res_1666_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1654_, v_us_1655_, v_useEq_boxed_1665_, v_ctorVal_1657_, v_params_1658_, v_type_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
if (lean_obj_tag(v_a_1667_) == 0)
{
lean_object* v___x_1669_; 
v___x_1669_ = l_List_reverse___redArg(v_a_1668_);
return v___x_1669_;
}
else
{
lean_object* v_head_1670_; lean_object* v_tail_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1680_; 
v_head_1670_ = lean_ctor_get(v_a_1667_, 0);
v_tail_1671_ = lean_ctor_get(v_a_1667_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_a_1667_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1673_ = v_a_1667_;
v_isShared_1674_ = v_isSharedCheck_1680_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_tail_1671_);
lean_inc(v_head_1670_);
lean_dec(v_a_1667_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1680_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1675_ = l_Lean_mkLevelParam(v_head_1670_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 1, v_a_1668_);
lean_ctor_set(v___x_1673_, 0, v___x_1675_);
v___x_1677_ = v___x_1673_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_a_1668_);
v___x_1677_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
v_a_1667_ = v_tail_1671_;
v_a_1668_ = v___x_1677_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1681_, uint8_t v_useEq_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_toConstantVal_1688_; lean_object* v_numParams_1689_; lean_object* v_name_1690_; lean_object* v_levelParams_1691_; lean_object* v_type_1692_; lean_object* v___x_1693_; 
v_toConstantVal_1688_ = lean_ctor_get(v_ctorVal_1681_, 0);
v_numParams_1689_ = lean_ctor_get(v_ctorVal_1681_, 3);
lean_inc(v_numParams_1689_);
v_name_1690_ = lean_ctor_get(v_toConstantVal_1688_, 0);
lean_inc(v_name_1690_);
v_levelParams_1691_ = lean_ctor_get(v_toConstantVal_1688_, 1);
v_type_1692_ = lean_ctor_get(v_toConstantVal_1688_, 2);
lean_inc_ref(v_type_1692_);
v___x_1693_ = l_Lean_Meta_elimOptParam(v_type_1692_, v_a_1685_, v_a_1686_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1695_; lean_object* v_us_1696_; lean_object* v___x_1697_; lean_object* v___f_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = lean_box(0);
lean_inc(v_levelParams_1691_);
v_us_1696_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1691_, v___x_1695_);
v___x_1697_ = lean_box(v_useEq_1682_);
v___f_1698_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1698_, 0, v_name_1690_);
lean_closure_set(v___f_1698_, 1, v_us_1696_);
lean_closure_set(v___f_1698_, 2, v___x_1697_);
lean_closure_set(v___f_1698_, 3, v_ctorVal_1681_);
v___x_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1699_, 0, v_numParams_1689_);
v___x_1700_ = 0;
v___x_1701_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1694_, v___x_1699_, v___f_1698_, v___x_1700_, v___x_1700_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
return v___x_1701_;
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_name_1690_);
lean_dec(v_numParams_1689_);
lean_dec_ref(v_ctorVal_1681_);
v_a_1702_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1693_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1693_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1710_, lean_object* v_useEq_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
uint8_t v_useEq_boxed_1717_; lean_object* v_res_1718_; 
v_useEq_boxed_1717_ = lean_unbox(v_useEq_1711_);
v_res_1718_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1710_, v_useEq_boxed_1717_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1719_, lean_object* v_bs_1720_, lean_object* v_k_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1720_, v_k_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1728_, lean_object* v_bs_1729_, lean_object* v_k_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1728_, v_bs_1729_, v_k_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec_ref(v_bs_1729_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1737_, lean_object* v_bs_1738_, lean_object* v_k_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1738_, v_k_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_bs_1747_, lean_object* v_k_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1746_, v_bs_1747_, v_k_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
uint8_t v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = 0;
v___x_1762_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1755_, v___x_1761_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
return v_res_1769_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
return v___x_1772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1776_){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1777_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1778_ = l_Lean_MessageData_ofName(v_ctorName_1776_);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1782_, lean_object* v_mvarId_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1789_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1782_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_mvarId_1783_);
v___x_1791_ = l_Lean_indentD(v___x_1790_);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1789_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1792_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1794_, lean_object* v_mvarId_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1794_, v_mvarId_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1802_, lean_object* v_ctorName_1803_, lean_object* v_mvarId_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1803_, v_mvarId_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1811_, lean_object* v_ctorName_1812_, lean_object* v_mvarId_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1811_, v_ctorName_1812_, v_mvarId_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1820_, lean_object* v_as_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
if (lean_obj_tag(v_as_1821_) == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec(v_ctorName_1820_);
v___x_1827_ = lean_box(0);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
else
{
lean_object* v_head_1829_; lean_object* v_tail_1830_; lean_object* v___x_1831_; 
v_head_1829_ = lean_ctor_get(v_as_1821_, 0);
lean_inc_n(v_head_1829_, 2);
v_tail_1830_ = lean_ctor_get(v_as_1821_, 1);
lean_inc(v_tail_1830_);
lean_dec_ref(v_as_1821_);
v___x_1831_ = l_Lean_MVarId_assumptionCore(v_head_1829_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; uint8_t v___x_1833_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref(v___x_1831_);
v___x_1833_ = lean_unbox(v_a_1832_);
lean_dec(v_a_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; 
lean_dec(v_tail_1830_);
v___x_1834_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1820_, v_head_1829_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
return v___x_1834_;
}
else
{
lean_dec(v_head_1829_);
v_as_1821_ = v_tail_1830_;
goto _start;
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_tail_1830_);
lean_dec(v_head_1829_);
lean_dec(v_ctorName_1820_);
v_a_1836_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1831_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1831_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1844_, lean_object* v_as_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1844_, v_as_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1852_, lean_object* v_ctorName_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_MVarId_splitAndCore(v_mvarId_1852_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1861_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1853_, v_a_1860_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
return v___x_1861_;
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_ctorName_1853_);
v_a_1862_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1859_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1859_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1870_, lean_object* v_ctorName_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1870_, v_ctorName_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___f_1885_; lean_object* v___x_1014__overap_1886_; lean_object* v___x_1887_; 
v___f_1885_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_1014__overap_1886_ = lean_panic_fn_borrowed(v___f_1885_, v_msg_1879_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
lean_inc(v___y_1881_);
lean_inc_ref(v___y_1880_);
v___x_1887_ = lean_apply_5(v___x_1014__overap_1886_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, lean_box(0));
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1894_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1895_; double v___x_1896_; 
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = lean_float_of_nat(v___x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1900_, lean_object* v_msg_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_ref_1907_; lean_object* v___x_1908_; lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1953_; 
v_ref_1907_ = lean_ctor_get(v___y_1904_, 5);
v___x_1908_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1953_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1953_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v_traceState_1914_; lean_object* v_env_1915_; lean_object* v_nextMacroScope_1916_; lean_object* v_ngen_1917_; lean_object* v_auxDeclNGen_1918_; lean_object* v_cache_1919_; lean_object* v_messages_1920_; lean_object* v_infoState_1921_; lean_object* v_snapshotTasks_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1952_; 
v___x_1913_ = lean_st_ref_take(v___y_1905_);
v_traceState_1914_ = lean_ctor_get(v___x_1913_, 4);
v_env_1915_ = lean_ctor_get(v___x_1913_, 0);
v_nextMacroScope_1916_ = lean_ctor_get(v___x_1913_, 1);
v_ngen_1917_ = lean_ctor_get(v___x_1913_, 2);
v_auxDeclNGen_1918_ = lean_ctor_get(v___x_1913_, 3);
v_cache_1919_ = lean_ctor_get(v___x_1913_, 5);
v_messages_1920_ = lean_ctor_get(v___x_1913_, 6);
v_infoState_1921_ = lean_ctor_get(v___x_1913_, 7);
v_snapshotTasks_1922_ = lean_ctor_get(v___x_1913_, 8);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1924_ = v___x_1913_;
v_isShared_1925_ = v_isSharedCheck_1952_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_snapshotTasks_1922_);
lean_inc(v_infoState_1921_);
lean_inc(v_messages_1920_);
lean_inc(v_cache_1919_);
lean_inc(v_traceState_1914_);
lean_inc(v_auxDeclNGen_1918_);
lean_inc(v_ngen_1917_);
lean_inc(v_nextMacroScope_1916_);
lean_inc(v_env_1915_);
lean_dec(v___x_1913_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1952_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
uint64_t v_tid_1926_; lean_object* v_traces_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1951_; 
v_tid_1926_ = lean_ctor_get_uint64(v_traceState_1914_, sizeof(void*)*1);
v_traces_1927_ = lean_ctor_get(v_traceState_1914_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_traceState_1914_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1929_ = v_traceState_1914_;
v_isShared_1930_ = v_isSharedCheck_1951_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_traces_1927_);
lean_dec(v_traceState_1914_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1951_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; double v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
v___x_1933_ = 0;
v___x_1934_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_1935_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1935_, 0, v_cls_1900_);
lean_ctor_set(v___x_1935_, 1, v___x_1931_);
lean_ctor_set(v___x_1935_, 2, v___x_1934_);
lean_ctor_set_float(v___x_1935_, sizeof(void*)*3, v___x_1932_);
lean_ctor_set_float(v___x_1935_, sizeof(void*)*3 + 8, v___x_1932_);
lean_ctor_set_uint8(v___x_1935_, sizeof(void*)*3 + 16, v___x_1933_);
v___x_1936_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__2));
v___x_1937_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v_a_1909_);
lean_ctor_set(v___x_1937_, 2, v___x_1936_);
lean_inc(v_ref_1907_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_ref_1907_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = l_Lean_PersistentArray_push___redArg(v_traces_1927_, v___x_1938_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v___x_1939_);
v___x_1941_ = v___x_1929_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1939_);
lean_ctor_set_uint64(v_reuseFailAlloc_1950_, sizeof(void*)*1, v_tid_1926_);
v___x_1941_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1943_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 4, v___x_1941_);
v___x_1943_ = v___x_1924_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_env_1915_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_nextMacroScope_1916_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_ngen_1917_);
lean_ctor_set(v_reuseFailAlloc_1949_, 3, v_auxDeclNGen_1918_);
lean_ctor_set(v_reuseFailAlloc_1949_, 4, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1949_, 5, v_cache_1919_);
lean_ctor_set(v_reuseFailAlloc_1949_, 6, v_messages_1920_);
lean_ctor_set(v_reuseFailAlloc_1949_, 7, v_infoState_1921_);
lean_ctor_set(v_reuseFailAlloc_1949_, 8, v_snapshotTasks_1922_);
v___x_1943_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1944_ = lean_st_ref_set(v___y_1905_, v___x_1943_);
v___x_1945_ = lean_box(0);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1945_);
v___x_1947_ = v___x_1911_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_1954_, lean_object* v_msg_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_1954_, v_msg_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
return v_res_1961_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1965_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_1966_ = lean_unsigned_to_nat(30u);
v___x_1967_ = lean_unsigned_to_nat(96u);
v___x_1968_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__1));
v___x_1969_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__0));
v___x_1970_ = l_mkPanicMessageWithDecl(v___x_1969_, v___x_1968_, v___x_1967_, v___x_1966_, v___x_1965_);
return v___x_1970_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9(void){
_start:
{
lean_object* v_cls_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_cls_1979_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_1980_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8));
v___x_1981_ = l_Lean_Name_append(v___x_1980_, v_cls_1979_);
return v___x_1981_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10));
v___x_1984_ = l_Lean_stringToMessageData(v___x_1983_);
return v___x_1984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12));
v___x_1987_ = l_Lean_stringToMessageData(v___x_1986_);
return v___x_1987_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__14));
v___x_1990_ = l_Lean_stringToMessageData(v___x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_1991_, lean_object* v_mvarId_1992_, lean_object* v_h_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v_options_2019_; uint8_t v_hasTrace_2020_; 
v_options_2019_ = lean_ctor_get(v_a_1996_, 2);
v_hasTrace_2020_ = lean_ctor_get_uint8(v_options_2019_, sizeof(void*)*1);
if (v_hasTrace_2020_ == 0)
{
v___y_2000_ = v_a_1994_;
v___y_2001_ = v_a_1995_;
v___y_2002_ = v_a_1996_;
v___y_2003_ = v_a_1997_;
goto v___jp_1999_;
}
else
{
lean_object* v_inheritedTraceOptions_2021_; lean_object* v_cls_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v_inheritedTraceOptions_2021_ = lean_ctor_get(v_a_1996_, 13);
v_cls_2022_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2023_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2024_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2021_, v_options_2019_, v___x_2023_);
if (v___x_2024_ == 0)
{
v___y_2000_ = v_a_1994_;
v___y_2001_ = v_a_1995_;
v___y_2002_ = v_a_1996_;
v___y_2003_ = v_a_1997_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2025_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11);
lean_inc(v_ctorName_1991_);
v___x_2026_ = l_Lean_MessageData_ofName(v_ctorName_1991_);
v___x_2027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2025_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__13);
v___x_2029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2027_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
lean_inc(v_h_1993_);
v___x_2030_ = l_Lean_mkFVar(v_h_1993_);
v___x_2031_ = l_Lean_MessageData_ofExpr(v___x_2030_);
v___x_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2029_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__15);
v___x_2034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
lean_inc(v_mvarId_1992_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_mvarId_1992_);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2022_, v___x_2036_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_dec_ref(v___x_2037_);
v___y_2000_ = v_a_1994_;
v___y_2001_ = v_a_1995_;
v___y_2002_ = v_a_1996_;
v___y_2003_ = v_a_1997_;
goto v___jp_1999_;
}
else
{
lean_dec(v_h_1993_);
lean_dec(v_mvarId_1992_);
lean_dec(v_ctorName_1991_);
return v___x_2037_;
}
}
}
v___jp_1999_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_box(0);
v___x_2005_ = l_Lean_Meta_injection(v_mvarId_1992_, v_h_1993_, v___x_2004_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref(v___x_2005_);
if (lean_obj_tag(v_a_2006_) == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec(v_ctorName_1991_);
v___x_2007_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2008_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2007_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
return v___x_2008_;
}
else
{
lean_object* v_mvarId_2009_; lean_object* v___x_2010_; 
v_mvarId_2009_ = lean_ctor_get(v_a_2006_, 0);
lean_inc(v_mvarId_2009_);
lean_dec_ref(v_a_2006_);
v___x_2010_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2009_, v_ctorName_1991_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
return v___x_2010_;
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_ctorName_1991_);
v_a_2011_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2005_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2005_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2038_, lean_object* v_mvarId_2039_, lean_object* v_h_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2038_, v_mvarId_2039_, v_h_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2047_, lean_object* v_k_2048_, uint8_t v_cleanupAnnotations_2049_, uint8_t v_whnfType_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___f_2056_; lean_object* v___x_2057_; 
v___f_2056_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2056_, 0, v_k_2048_);
v___x_2057_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2047_, v___f_2056_, v_cleanupAnnotations_2049_, v_whnfType_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
v_a_2066_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2057_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2057_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2074_, lean_object* v_k_2075_, lean_object* v_cleanupAnnotations_2076_, lean_object* v_whnfType_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2083_; uint8_t v_whnfType_boxed_2084_; lean_object* v_res_2085_; 
v_cleanupAnnotations_boxed_2083_ = lean_unbox(v_cleanupAnnotations_2076_);
v_whnfType_boxed_2084_ = lean_unbox(v_whnfType_2077_);
v_res_2085_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2074_, v_k_2075_, v_cleanupAnnotations_boxed_2083_, v_whnfType_boxed_2084_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2086_, lean_object* v_type_2087_, lean_object* v_k_2088_, uint8_t v_cleanupAnnotations_2089_, uint8_t v_whnfType_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2087_, v_k_2088_, v_cleanupAnnotations_2089_, v_whnfType_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2097_, lean_object* v_type_2098_, lean_object* v_k_2099_, lean_object* v_cleanupAnnotations_2100_, lean_object* v_whnfType_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2107_; uint8_t v_whnfType_boxed_2108_; lean_object* v_res_2109_; 
v_cleanupAnnotations_boxed_2107_ = lean_unbox(v_cleanupAnnotations_2100_);
v_whnfType_boxed_2108_ = lean_unbox(v_whnfType_2101_);
v_res_2109_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2097_, v_type_2098_, v_k_2099_, v_cleanupAnnotations_boxed_2107_, v_whnfType_boxed_2108_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2110_, lean_object* v_ctorName_2111_, lean_object* v_xs_2112_, lean_object* v_type_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_box(0);
v___x_2120_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2113_, v___x_2119_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
v___x_2122_ = l_Lean_Expr_mvarId_x21(v_a_2121_);
v___x_2123_ = lean_array_get_size(v_xs_2112_);
v___x_2124_ = lean_unsigned_to_nat(1u);
v___x_2125_ = lean_nat_sub(v___x_2123_, v___x_2124_);
v___x_2126_ = lean_array_get_borrowed(v___x_2110_, v_xs_2112_, v___x_2125_);
lean_dec(v___x_2125_);
v___x_2127_ = l_Lean_Expr_fvarId_x21(v___x_2126_);
v___x_2128_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2111_, v___x_2122_, v___x_2127_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
if (lean_obj_tag(v___x_2128_) == 0)
{
uint8_t v___x_2129_; uint8_t v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; 
lean_dec_ref(v___x_2128_);
v___x_2129_ = 0;
v___x_2130_ = 1;
v___x_2131_ = 1;
v___x_2132_ = l_Lean_Meta_mkLambdaFVars(v_xs_2112_, v_a_2121_, v___x_2129_, v___x_2130_, v___x_2129_, v___x_2130_, v___x_2131_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
return v___x_2132_;
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_a_2121_);
v_a_2133_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2128_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2128_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
else
{
lean_dec(v_ctorName_2111_);
return v___x_2120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2141_, lean_object* v_ctorName_2142_, lean_object* v_xs_2143_, lean_object* v_type_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2141_, v_ctorName_2142_, v_xs_2143_, v_type_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec_ref(v_xs_2143_);
lean_dec_ref(v___x_2141_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2151_, lean_object* v_targetType_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___x_2158_; lean_object* v___f_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; 
v___x_2158_ = l_Lean_instInhabitedExpr;
v___f_2159_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2159_, 0, v___x_2158_);
lean_closure_set(v___f_2159_, 1, v_ctorName_2151_);
v___x_2160_ = 0;
v___x_2161_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2152_, v___f_2159_, v___x_2160_, v___x_2160_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2162_, lean_object* v_targetType_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2162_, v_targetType_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2175_ = l_Lean_Name_append(v_ctorName_2173_, v___x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v___x_2179_; 
v___x_2179_ = l_Lean_Expr_hasMVar(v_e_2176_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v_e_2176_);
return v___x_2180_;
}
else
{
lean_object* v___x_2181_; lean_object* v_mctx_2182_; lean_object* v___x_2183_; lean_object* v_fst_2184_; lean_object* v_snd_2185_; lean_object* v___x_2186_; lean_object* v_cache_2187_; lean_object* v_zetaDeltaFVarIds_2188_; lean_object* v_postponed_2189_; lean_object* v_diag_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2199_; 
v___x_2181_ = lean_st_ref_get(v___y_2177_);
v_mctx_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc_ref(v_mctx_2182_);
lean_dec(v___x_2181_);
v___x_2183_ = l_Lean_instantiateMVarsCore(v_mctx_2182_, v_e_2176_);
v_fst_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_fst_2184_);
v_snd_2185_ = lean_ctor_get(v___x_2183_, 1);
lean_inc(v_snd_2185_);
lean_dec_ref(v___x_2183_);
v___x_2186_ = lean_st_ref_take(v___y_2177_);
v_cache_2187_ = lean_ctor_get(v___x_2186_, 1);
v_zetaDeltaFVarIds_2188_ = lean_ctor_get(v___x_2186_, 2);
v_postponed_2189_ = lean_ctor_get(v___x_2186_, 3);
v_diag_2190_ = lean_ctor_get(v___x_2186_, 4);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v___x_2186_, 0);
lean_dec(v_unused_2200_);
v___x_2192_ = v___x_2186_;
v_isShared_2193_ = v_isSharedCheck_2199_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_diag_2190_);
lean_inc(v_postponed_2189_);
lean_inc(v_zetaDeltaFVarIds_2188_);
lean_inc(v_cache_2187_);
lean_dec(v___x_2186_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2199_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_snd_2185_);
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_snd_2185_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_cache_2187_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_zetaDeltaFVarIds_2188_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_postponed_2189_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_diag_2190_);
v___x_2195_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_st_ref_set(v___y_2177_, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v_fst_2184_);
return v___x_2197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2201_, v___y_2202_);
lean_dec(v___y_2202_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2205_, v___y_2207_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
return v_res_2218_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_unsigned_to_nat(32u);
v___x_2220_ = lean_mk_empty_array_with_capacity(v___x_2219_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2222_ = ((size_t)5ULL);
v___x_2223_ = lean_unsigned_to_nat(0u);
v___x_2224_ = lean_unsigned_to_nat(32u);
v___x_2225_ = lean_mk_empty_array_with_capacity(v___x_2224_);
v___x_2226_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2227_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v___x_2225_);
lean_ctor_set(v___x_2227_, 2, v___x_2223_);
lean_ctor_set(v___x_2227_, 3, v___x_2223_);
lean_ctor_set_usize(v___x_2227_, 4, v___x_2222_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; lean_object* v_traceState_2231_; lean_object* v_traces_2232_; lean_object* v___x_2233_; lean_object* v_traceState_2234_; lean_object* v_env_2235_; lean_object* v_nextMacroScope_2236_; lean_object* v_ngen_2237_; lean_object* v_auxDeclNGen_2238_; lean_object* v_cache_2239_; lean_object* v_messages_2240_; lean_object* v_infoState_2241_; lean_object* v_snapshotTasks_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2261_; 
v___x_2230_ = lean_st_ref_get(v___y_2228_);
v_traceState_2231_ = lean_ctor_get(v___x_2230_, 4);
lean_inc_ref(v_traceState_2231_);
lean_dec(v___x_2230_);
v_traces_2232_ = lean_ctor_get(v_traceState_2231_, 0);
lean_inc_ref(v_traces_2232_);
lean_dec_ref(v_traceState_2231_);
v___x_2233_ = lean_st_ref_take(v___y_2228_);
v_traceState_2234_ = lean_ctor_get(v___x_2233_, 4);
v_env_2235_ = lean_ctor_get(v___x_2233_, 0);
v_nextMacroScope_2236_ = lean_ctor_get(v___x_2233_, 1);
v_ngen_2237_ = lean_ctor_get(v___x_2233_, 2);
v_auxDeclNGen_2238_ = lean_ctor_get(v___x_2233_, 3);
v_cache_2239_ = lean_ctor_get(v___x_2233_, 5);
v_messages_2240_ = lean_ctor_get(v___x_2233_, 6);
v_infoState_2241_ = lean_ctor_get(v___x_2233_, 7);
v_snapshotTasks_2242_ = lean_ctor_get(v___x_2233_, 8);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2244_ = v___x_2233_;
v_isShared_2245_ = v_isSharedCheck_2261_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_snapshotTasks_2242_);
lean_inc(v_infoState_2241_);
lean_inc(v_messages_2240_);
lean_inc(v_cache_2239_);
lean_inc(v_traceState_2234_);
lean_inc(v_auxDeclNGen_2238_);
lean_inc(v_ngen_2237_);
lean_inc(v_nextMacroScope_2236_);
lean_inc(v_env_2235_);
lean_dec(v___x_2233_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2261_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
uint64_t v_tid_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2259_; 
v_tid_2246_ = lean_ctor_get_uint64(v_traceState_2234_, sizeof(void*)*1);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_traceState_2234_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; 
v_unused_2260_ = lean_ctor_get(v_traceState_2234_, 0);
lean_dec(v_unused_2260_);
v___x_2248_ = v_traceState_2234_;
v_isShared_2249_ = v_isSharedCheck_2259_;
goto v_resetjp_2247_;
}
else
{
lean_dec(v_traceState_2234_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2259_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2250_);
v___x_2252_ = v___x_2248_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2250_);
lean_ctor_set_uint64(v_reuseFailAlloc_2258_, sizeof(void*)*1, v_tid_2246_);
v___x_2252_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2254_; 
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 4, v___x_2252_);
v___x_2254_ = v___x_2244_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_env_2235_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_nextMacroScope_2236_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_ngen_2237_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v_auxDeclNGen_2238_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2257_, 5, v_cache_2239_);
lean_ctor_set(v_reuseFailAlloc_2257_, 6, v_messages_2240_);
lean_ctor_set(v_reuseFailAlloc_2257_, 7, v_infoState_2241_);
lean_ctor_set(v_reuseFailAlloc_2257_, 8, v_snapshotTasks_2242_);
v___x_2254_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_st_ref_set(v___y_2228_, v___x_2254_);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v_traces_2232_);
return v___x_2256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2262_);
lean_dec(v___y_2262_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
return v_res_2276_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2277_, lean_object* v_opt_2278_){
_start:
{
lean_object* v_name_2279_; lean_object* v_defValue_2280_; lean_object* v_map_2281_; lean_object* v___x_2282_; 
v_name_2279_ = lean_ctor_get(v_opt_2278_, 0);
v_defValue_2280_ = lean_ctor_get(v_opt_2278_, 1);
v_map_2281_ = lean_ctor_get(v_opts_2277_, 0);
v___x_2282_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2281_, v_name_2279_);
if (lean_obj_tag(v___x_2282_) == 0)
{
uint8_t v___x_2283_; 
v___x_2283_ = lean_unbox(v_defValue_2280_);
return v___x_2283_;
}
else
{
lean_object* v_val_2284_; 
v_val_2284_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_val_2284_);
lean_dec_ref(v___x_2282_);
if (lean_obj_tag(v_val_2284_) == 1)
{
uint8_t v_v_2285_; 
v_v_2285_ = lean_ctor_get_uint8(v_val_2284_, 0);
lean_dec_ref(v_val_2284_);
return v_v_2285_;
}
else
{
uint8_t v___x_2286_; 
lean_dec(v_val_2284_);
v___x_2286_ = lean_unbox(v_defValue_2280_);
return v___x_2286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2287_, lean_object* v_opt_2288_){
_start:
{
uint8_t v_res_2289_; lean_object* v_r_2290_; 
v_res_2289_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2287_, v_opt_2288_);
lean_dec_ref(v_opt_2288_);
lean_dec_ref(v_opts_2287_);
v_r_2290_ = lean_box(v_res_2289_);
return v_r_2290_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2293_ = l_Lean_stringToMessageData(v___x_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2294_, lean_object* v_x_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2301_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2302_ = l_Lean_MessageData_ofName(v_name_2294_);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2307_, lean_object* v_x_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2307_, v_x_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v_x_2308_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2315_, lean_object* v_val_2316_, lean_object* v_name_2317_, lean_object* v_levelParams_2318_, uint8_t v___x_2319_, lean_object* v_____r_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v___x_2326_; 
lean_inc_ref(v_val_2316_);
v___x_2326_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2315_, v_val_2316_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2328_; lean_object* v_a_2329_; lean_object* v___x_2330_; lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2343_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref(v___x_2326_);
v___x_2328_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2316_, v___y_2322_);
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2327_, v___y_2322_);
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2343_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2343_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
lean_inc(v_name_2317_);
v___x_2335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2335_, 0, v_name_2317_);
lean_ctor_set(v___x_2335_, 1, v_levelParams_2318_);
lean_ctor_set(v___x_2335_, 2, v_a_2329_);
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2337_, 0, v_name_2317_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2335_);
lean_ctor_set(v___x_2338_, 1, v_a_2331_);
lean_ctor_set(v___x_2338_, 2, v___x_2337_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set_tag(v___x_2333_, 2);
lean_ctor_set(v___x_2333_, 0, v___x_2338_);
v___x_2340_ = v___x_2333_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_addDecl(v___x_2340_, v___x_2319_, v___y_2323_, v___y_2324_);
return v___x_2341_;
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v_levelParams_2318_);
lean_dec(v_name_2317_);
lean_dec_ref(v_val_2316_);
v_a_2344_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2326_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2326_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2352_, lean_object* v_val_2353_, lean_object* v_name_2354_, lean_object* v_levelParams_2355_, lean_object* v___x_2356_, lean_object* v_____r_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
uint8_t v___x_12938__boxed_2363_; lean_object* v_res_2364_; 
v___x_12938__boxed_2363_ = lean_unbox(v___x_2356_);
v_res_2364_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2352_, v_val_2353_, v_name_2354_, v_levelParams_2355_, v___x_12938__boxed_2363_, v_____r_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2365_, lean_object* v_val_2366_, lean_object* v_name_2367_, lean_object* v_levelParams_2368_, lean_object* v_____r_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v___x_2375_; 
lean_inc_ref(v_val_2366_);
v___x_2375_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2365_, v_val_2366_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2377_; lean_object* v_a_2378_; lean_object* v___x_2379_; lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2393_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref(v___x_2375_);
v___x_2377_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2366_, v___y_2371_);
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2376_, v___y_2371_);
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2393_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2393_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
lean_inc(v_name_2367_);
v___x_2384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2384_, 0, v_name_2367_);
lean_ctor_set(v___x_2384_, 1, v_levelParams_2368_);
lean_ctor_set(v___x_2384_, 2, v_a_2378_);
v___x_2385_ = lean_box(0);
v___x_2386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2386_, 0, v_name_2367_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2384_);
lean_ctor_set(v___x_2387_, 1, v_a_2380_);
lean_ctor_set(v___x_2387_, 2, v___x_2386_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 2);
lean_ctor_set(v___x_2382_, 0, v___x_2387_);
v___x_2389_ = v___x_2382_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
uint8_t v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = 0;
v___x_2391_ = l_Lean_addDecl(v___x_2389_, v___x_2390_, v___y_2372_, v___y_2373_);
return v___x_2391_;
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec(v_levelParams_2368_);
lean_dec(v_name_2367_);
lean_dec_ref(v_val_2366_);
v_a_2394_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2375_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2375_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2402_, lean_object* v_val_2403_, lean_object* v_name_2404_, lean_object* v_levelParams_2405_, lean_object* v_____r_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2402_, v_val_2403_, v_name_2404_, v_levelParams_2405_, v_____r_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2412_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_e_2413_){
_start:
{
if (lean_obj_tag(v_e_2413_) == 0)
{
uint8_t v___x_2414_; 
v___x_2414_ = 2;
return v___x_2414_;
}
else
{
uint8_t v___x_2415_; 
v___x_2415_ = 0;
return v___x_2415_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_e_2416_){
_start:
{
uint8_t v_res_2417_; lean_object* v_r_2418_; 
v_res_2417_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_e_2416_);
lean_dec_ref(v_e_2416_);
v_r_2418_ = lean_box(v_res_2417_);
return v_r_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2419_, lean_object* v_opt_2420_){
_start:
{
lean_object* v_name_2421_; lean_object* v_defValue_2422_; lean_object* v_map_2423_; lean_object* v___x_2424_; 
v_name_2421_ = lean_ctor_get(v_opt_2420_, 0);
v_defValue_2422_ = lean_ctor_get(v_opt_2420_, 1);
v_map_2423_ = lean_ctor_get(v_opts_2419_, 0);
v___x_2424_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2423_, v_name_2421_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_inc(v_defValue_2422_);
return v_defValue_2422_;
}
else
{
lean_object* v_val_2425_; 
v_val_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_val_2425_);
lean_dec_ref(v___x_2424_);
if (lean_obj_tag(v_val_2425_) == 3)
{
lean_object* v_v_2426_; 
v_v_2426_ = lean_ctor_get(v_val_2425_, 0);
lean_inc(v_v_2426_);
lean_dec_ref(v_val_2425_);
return v_v_2426_;
}
else
{
lean_dec(v_val_2425_);
lean_inc(v_defValue_2422_);
return v_defValue_2422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2427_, lean_object* v_opt_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2427_, v_opt_2428_);
lean_dec_ref(v_opt_2428_);
lean_dec_ref(v_opts_2427_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(lean_object* v_x_2430_){
_start:
{
if (lean_obj_tag(v_x_2430_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
v_a_2432_ = lean_ctor_get(v_x_2430_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_x_2430_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v_x_2430_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v_x_2430_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set_tag(v___x_2434_, 1);
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
v_a_2440_ = lean_ctor_get(v_x_2430_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_x_2430_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v_x_2430_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v_x_2430_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
lean_ctor_set_tag(v___x_2442_, 0);
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg___boxed(lean_object* v_x_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2448_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(size_t v_sz_2451_, size_t v_i_2452_, lean_object* v_bs_2453_){
_start:
{
uint8_t v___x_2454_; 
v___x_2454_ = lean_usize_dec_lt(v_i_2452_, v_sz_2451_);
if (v___x_2454_ == 0)
{
return v_bs_2453_;
}
else
{
lean_object* v_v_2455_; lean_object* v_msg_2456_; lean_object* v___x_2457_; lean_object* v_bs_x27_2458_; size_t v___x_2459_; size_t v___x_2460_; lean_object* v___x_2461_; 
v_v_2455_ = lean_array_uget_borrowed(v_bs_2453_, v_i_2452_);
v_msg_2456_ = lean_ctor_get(v_v_2455_, 1);
lean_inc_ref(v_msg_2456_);
v___x_2457_ = lean_unsigned_to_nat(0u);
v_bs_x27_2458_ = lean_array_uset(v_bs_2453_, v_i_2452_, v___x_2457_);
v___x_2459_ = ((size_t)1ULL);
v___x_2460_ = lean_usize_add(v_i_2452_, v___x_2459_);
v___x_2461_ = lean_array_uset(v_bs_x27_2458_, v_i_2452_, v_msg_2456_);
v_i_2452_ = v___x_2460_;
v_bs_2453_ = v___x_2461_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_2463_, lean_object* v_i_2464_, lean_object* v_bs_2465_){
_start:
{
size_t v_sz_boxed_2466_; size_t v_i_boxed_2467_; lean_object* v_res_2468_; 
v_sz_boxed_2466_ = lean_unbox_usize(v_sz_2463_);
lean_dec(v_sz_2463_);
v_i_boxed_2467_ = lean_unbox_usize(v_i_2464_);
lean_dec(v_i_2464_);
v_res_2468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_boxed_2466_, v_i_boxed_2467_, v_bs_2465_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_oldTraces_2469_, lean_object* v_data_2470_, lean_object* v_ref_2471_, lean_object* v_msg_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_fileName_2478_; lean_object* v_fileMap_2479_; lean_object* v_options_2480_; lean_object* v_currRecDepth_2481_; lean_object* v_maxRecDepth_2482_; lean_object* v_ref_2483_; lean_object* v_currNamespace_2484_; lean_object* v_openDecls_2485_; lean_object* v_initHeartbeats_2486_; lean_object* v_maxHeartbeats_2487_; lean_object* v_quotContext_2488_; lean_object* v_currMacroScope_2489_; uint8_t v_diag_2490_; lean_object* v_cancelTk_x3f_2491_; uint8_t v_suppressElabErrors_2492_; lean_object* v_inheritedTraceOptions_2493_; lean_object* v___x_2494_; lean_object* v_traceState_2495_; lean_object* v_traces_2496_; lean_object* v_ref_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; size_t v_sz_2500_; size_t v___x_2501_; lean_object* v___x_2502_; lean_object* v_msg_2503_; lean_object* v___x_2504_; lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2542_; 
v_fileName_2478_ = lean_ctor_get(v___y_2475_, 0);
v_fileMap_2479_ = lean_ctor_get(v___y_2475_, 1);
v_options_2480_ = lean_ctor_get(v___y_2475_, 2);
v_currRecDepth_2481_ = lean_ctor_get(v___y_2475_, 3);
v_maxRecDepth_2482_ = lean_ctor_get(v___y_2475_, 4);
v_ref_2483_ = lean_ctor_get(v___y_2475_, 5);
v_currNamespace_2484_ = lean_ctor_get(v___y_2475_, 6);
v_openDecls_2485_ = lean_ctor_get(v___y_2475_, 7);
v_initHeartbeats_2486_ = lean_ctor_get(v___y_2475_, 8);
v_maxHeartbeats_2487_ = lean_ctor_get(v___y_2475_, 9);
v_quotContext_2488_ = lean_ctor_get(v___y_2475_, 10);
v_currMacroScope_2489_ = lean_ctor_get(v___y_2475_, 11);
v_diag_2490_ = lean_ctor_get_uint8(v___y_2475_, sizeof(void*)*14);
v_cancelTk_x3f_2491_ = lean_ctor_get(v___y_2475_, 12);
v_suppressElabErrors_2492_ = lean_ctor_get_uint8(v___y_2475_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2493_ = lean_ctor_get(v___y_2475_, 13);
v___x_2494_ = lean_st_ref_get(v___y_2476_);
v_traceState_2495_ = lean_ctor_get(v___x_2494_, 4);
lean_inc_ref(v_traceState_2495_);
lean_dec(v___x_2494_);
v_traces_2496_ = lean_ctor_get(v_traceState_2495_, 0);
lean_inc_ref(v_traces_2496_);
lean_dec_ref(v_traceState_2495_);
v_ref_2497_ = l_Lean_replaceRef(v_ref_2471_, v_ref_2483_);
lean_inc_ref(v_inheritedTraceOptions_2493_);
lean_inc(v_cancelTk_x3f_2491_);
lean_inc(v_currMacroScope_2489_);
lean_inc(v_quotContext_2488_);
lean_inc(v_maxHeartbeats_2487_);
lean_inc(v_initHeartbeats_2486_);
lean_inc(v_openDecls_2485_);
lean_inc(v_currNamespace_2484_);
lean_inc(v_maxRecDepth_2482_);
lean_inc(v_currRecDepth_2481_);
lean_inc_ref(v_options_2480_);
lean_inc_ref(v_fileMap_2479_);
lean_inc_ref(v_fileName_2478_);
v___x_2498_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2498_, 0, v_fileName_2478_);
lean_ctor_set(v___x_2498_, 1, v_fileMap_2479_);
lean_ctor_set(v___x_2498_, 2, v_options_2480_);
lean_ctor_set(v___x_2498_, 3, v_currRecDepth_2481_);
lean_ctor_set(v___x_2498_, 4, v_maxRecDepth_2482_);
lean_ctor_set(v___x_2498_, 5, v_ref_2497_);
lean_ctor_set(v___x_2498_, 6, v_currNamespace_2484_);
lean_ctor_set(v___x_2498_, 7, v_openDecls_2485_);
lean_ctor_set(v___x_2498_, 8, v_initHeartbeats_2486_);
lean_ctor_set(v___x_2498_, 9, v_maxHeartbeats_2487_);
lean_ctor_set(v___x_2498_, 10, v_quotContext_2488_);
lean_ctor_set(v___x_2498_, 11, v_currMacroScope_2489_);
lean_ctor_set(v___x_2498_, 12, v_cancelTk_x3f_2491_);
lean_ctor_set(v___x_2498_, 13, v_inheritedTraceOptions_2493_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*14, v_diag_2490_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*14 + 1, v_suppressElabErrors_2492_);
v___x_2499_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2496_);
lean_dec_ref(v_traces_2496_);
v_sz_2500_ = lean_array_size(v___x_2499_);
v___x_2501_ = ((size_t)0ULL);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_2500_, v___x_2501_, v___x_2499_);
v_msg_2503_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2503_, 0, v_data_2470_);
lean_ctor_set(v_msg_2503_, 1, v_msg_2472_);
lean_ctor_set(v_msg_2503_, 2, v___x_2502_);
v___x_2504_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2503_, v___y_2473_, v___y_2474_, v___x_2498_, v___y_2476_);
lean_dec_ref(v___x_2498_);
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2542_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2542_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v_traceState_2510_; lean_object* v_env_2511_; lean_object* v_nextMacroScope_2512_; lean_object* v_ngen_2513_; lean_object* v_auxDeclNGen_2514_; lean_object* v_cache_2515_; lean_object* v_messages_2516_; lean_object* v_infoState_2517_; lean_object* v_snapshotTasks_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2541_; 
v___x_2509_ = lean_st_ref_take(v___y_2476_);
v_traceState_2510_ = lean_ctor_get(v___x_2509_, 4);
v_env_2511_ = lean_ctor_get(v___x_2509_, 0);
v_nextMacroScope_2512_ = lean_ctor_get(v___x_2509_, 1);
v_ngen_2513_ = lean_ctor_get(v___x_2509_, 2);
v_auxDeclNGen_2514_ = lean_ctor_get(v___x_2509_, 3);
v_cache_2515_ = lean_ctor_get(v___x_2509_, 5);
v_messages_2516_ = lean_ctor_get(v___x_2509_, 6);
v_infoState_2517_ = lean_ctor_get(v___x_2509_, 7);
v_snapshotTasks_2518_ = lean_ctor_get(v___x_2509_, 8);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2520_ = v___x_2509_;
v_isShared_2521_ = v_isSharedCheck_2541_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_snapshotTasks_2518_);
lean_inc(v_infoState_2517_);
lean_inc(v_messages_2516_);
lean_inc(v_cache_2515_);
lean_inc(v_traceState_2510_);
lean_inc(v_auxDeclNGen_2514_);
lean_inc(v_ngen_2513_);
lean_inc(v_nextMacroScope_2512_);
lean_inc(v_env_2511_);
lean_dec(v___x_2509_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2541_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
uint64_t v_tid_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2539_; 
v_tid_2522_ = lean_ctor_get_uint64(v_traceState_2510_, sizeof(void*)*1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_traceState_2510_);
if (v_isSharedCheck_2539_ == 0)
{
lean_object* v_unused_2540_; 
v_unused_2540_ = lean_ctor_get(v_traceState_2510_, 0);
lean_dec(v_unused_2540_);
v___x_2524_ = v_traceState_2510_;
v_isShared_2525_ = v_isSharedCheck_2539_;
goto v_resetjp_2523_;
}
else
{
lean_dec(v_traceState_2510_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2539_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_ref_2471_);
lean_ctor_set(v___x_2526_, 1, v_a_2505_);
v___x_2527_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2469_, v___x_2526_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2527_);
v___x_2529_ = v___x_2524_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2527_);
lean_ctor_set_uint64(v_reuseFailAlloc_2538_, sizeof(void*)*1, v_tid_2522_);
v___x_2529_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2531_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 4, v___x_2529_);
v___x_2531_ = v___x_2520_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_env_2511_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_nextMacroScope_2512_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_ngen_2513_);
lean_ctor_set(v_reuseFailAlloc_2537_, 3, v_auxDeclNGen_2514_);
lean_ctor_set(v_reuseFailAlloc_2537_, 4, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2537_, 5, v_cache_2515_);
lean_ctor_set(v_reuseFailAlloc_2537_, 6, v_messages_2516_);
lean_ctor_set(v_reuseFailAlloc_2537_, 7, v_infoState_2517_);
lean_ctor_set(v_reuseFailAlloc_2537_, 8, v_snapshotTasks_2518_);
v___x_2531_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2532_ = lean_st_ref_set(v___y_2476_, v___x_2531_);
v___x_2533_ = lean_box(0);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2533_);
v___x_2535_ = v___x_2507_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_oldTraces_2543_, lean_object* v_data_2544_, lean_object* v_ref_2545_, lean_object* v_msg_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2543_, v_data_2544_, v_ref_2545_, v_msg_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2552_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2));
v___x_2558_ = l_Lean_stringToMessageData(v___x_2557_);
return v___x_2558_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2559_; double v___x_2560_; 
v___x_2559_ = lean_unsigned_to_nat(1000u);
v___x_2560_ = lean_float_of_nat(v___x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2561_, uint8_t v_collapsed_2562_, lean_object* v_tag_2563_, lean_object* v_opts_2564_, uint8_t v_clsEnabled_2565_, lean_object* v_oldTraces_2566_, lean_object* v_msg_2567_, lean_object* v_resStartStop_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_fst_2574_; lean_object* v_snd_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2665_; 
v_fst_2574_ = lean_ctor_get(v_resStartStop_2568_, 0);
v_snd_2575_ = lean_ctor_get(v_resStartStop_2568_, 1);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_resStartStop_2568_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2577_ = v_resStartStop_2568_;
v_isShared_2578_ = v_isSharedCheck_2665_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_snd_2575_);
lean_inc(v_fst_2574_);
lean_dec(v_resStartStop_2568_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2665_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v_data_2582_; lean_object* v_fst_2585_; lean_object* v_snd_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2664_; 
v_fst_2585_ = lean_ctor_get(v_snd_2575_, 0);
v_snd_2586_ = lean_ctor_get(v_snd_2575_, 1);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_snd_2575_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2588_ = v_snd_2575_;
v_isShared_2589_ = v_isSharedCheck_2664_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_snd_2586_);
lean_inc(v_fst_2585_);
lean_dec(v_snd_2575_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2664_;
goto v_resetjp_2587_;
}
v___jp_2579_:
{
lean_object* v___x_2583_; 
lean_inc(v___y_2581_);
v___x_2583_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2566_, v_data_2582_, v___y_2581_, v___y_2580_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v___x_2584_; 
lean_dec_ref(v___x_2583_);
v___x_2584_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2574_);
return v___x_2584_;
}
else
{
lean_dec(v_fst_2574_);
return v___x_2583_;
}
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___y_2593_; lean_object* v_a_2594_; uint8_t v___y_2618_; double v___y_2649_; 
v___x_2590_ = l_Lean_trace_profiler;
v___x_2591_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2564_, v___x_2590_);
if (v___x_2591_ == 0)
{
v___y_2618_ = v___x_2591_;
goto v___jp_2617_;
}
else
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2655_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2564_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; lean_object* v___x_2657_; double v___x_2658_; double v___x_2659_; double v___x_2660_; 
v___x_2656_ = l_Lean_trace_profiler_threshold;
v___x_2657_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2564_, v___x_2656_);
v___x_2658_ = lean_float_of_nat(v___x_2657_);
v___x_2659_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4);
v___x_2660_ = lean_float_div(v___x_2658_, v___x_2659_);
v___y_2649_ = v___x_2660_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; double v___x_2663_; 
v___x_2661_ = l_Lean_trace_profiler_threshold;
v___x_2662_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2564_, v___x_2661_);
v___x_2663_ = lean_float_of_nat(v___x_2662_);
v___y_2649_ = v___x_2663_;
goto v___jp_2648_;
}
}
v___jp_2592_:
{
uint8_t v_result_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v_result_2595_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_fst_2574_);
v___x_2596_ = l_Lean_TraceResult_toEmoji(v_result_2595_);
v___x_2597_ = l_Lean_stringToMessageData(v___x_2596_);
v___x_2598_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
if (v_isShared_2589_ == 0)
{
lean_ctor_set_tag(v___x_2588_, 7);
lean_ctor_set(v___x_2588_, 1, v___x_2598_);
lean_ctor_set(v___x_2588_, 0, v___x_2597_);
v___x_2600_ = v___x_2588_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v_m_2602_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set_tag(v___x_2577_, 7);
lean_ctor_set(v___x_2577_, 1, v_a_2594_);
lean_ctor_set(v___x_2577_, 0, v___x_2600_);
v_m_2602_ = v___x_2577_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_a_2594_);
v_m_2602_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; double v___x_2605_; lean_object* v_data_2606_; 
v___x_2603_ = lean_box(v_result_2595_);
v___x_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
v___x_2605_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__0);
lean_inc_ref(v_tag_2563_);
lean_inc_ref(v___x_2604_);
lean_inc(v_cls_2561_);
v_data_2606_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2606_, 0, v_cls_2561_);
lean_ctor_set(v_data_2606_, 1, v___x_2604_);
lean_ctor_set(v_data_2606_, 2, v_tag_2563_);
lean_ctor_set_float(v_data_2606_, sizeof(void*)*3, v___x_2605_);
lean_ctor_set_float(v_data_2606_, sizeof(void*)*3 + 8, v___x_2605_);
lean_ctor_set_uint8(v_data_2606_, sizeof(void*)*3 + 16, v_collapsed_2562_);
if (v___x_2591_ == 0)
{
lean_dec_ref(v___x_2604_);
lean_dec(v_snd_2586_);
lean_dec(v_fst_2585_);
lean_dec_ref(v_tag_2563_);
lean_dec(v_cls_2561_);
v___y_2580_ = v_m_2602_;
v___y_2581_ = v___y_2593_;
v_data_2582_ = v_data_2606_;
goto v___jp_2579_;
}
else
{
lean_object* v_data_2607_; double v___x_2608_; double v___x_2609_; 
lean_dec_ref(v_data_2606_);
v_data_2607_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2607_, 0, v_cls_2561_);
lean_ctor_set(v_data_2607_, 1, v___x_2604_);
lean_ctor_set(v_data_2607_, 2, v_tag_2563_);
v___x_2608_ = lean_unbox_float(v_fst_2585_);
lean_dec(v_fst_2585_);
lean_ctor_set_float(v_data_2607_, sizeof(void*)*3, v___x_2608_);
v___x_2609_ = lean_unbox_float(v_snd_2586_);
lean_dec(v_snd_2586_);
lean_ctor_set_float(v_data_2607_, sizeof(void*)*3 + 8, v___x_2609_);
lean_ctor_set_uint8(v_data_2607_, sizeof(void*)*3 + 16, v_collapsed_2562_);
v___y_2580_ = v_m_2602_;
v___y_2581_ = v___y_2593_;
v_data_2582_ = v_data_2607_;
goto v___jp_2579_;
}
}
}
}
v___jp_2612_:
{
lean_object* v_ref_2613_; lean_object* v___x_2614_; 
v_ref_2613_ = lean_ctor_get(v___y_2571_, 5);
lean_inc(v___y_2572_);
lean_inc_ref(v___y_2571_);
lean_inc(v___y_2570_);
lean_inc_ref(v___y_2569_);
lean_inc(v_fst_2574_);
v___x_2614_ = lean_apply_6(v_msg_2567_, v_fst_2574_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, lean_box(0));
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref(v___x_2614_);
v___y_2593_ = v_ref_2613_;
v_a_2594_ = v_a_2615_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2616_; 
lean_dec_ref(v___x_2614_);
v___x_2616_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3);
v___y_2593_ = v_ref_2613_;
v_a_2594_ = v___x_2616_;
goto v___jp_2592_;
}
}
v___jp_2617_:
{
if (v_clsEnabled_2565_ == 0)
{
if (v___y_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v_traceState_2620_; lean_object* v_env_2621_; lean_object* v_nextMacroScope_2622_; lean_object* v_ngen_2623_; lean_object* v_auxDeclNGen_2624_; lean_object* v_cache_2625_; lean_object* v_messages_2626_; lean_object* v_infoState_2627_; lean_object* v_snapshotTasks_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2647_; 
lean_del_object(v___x_2588_);
lean_dec(v_snd_2586_);
lean_dec(v_fst_2585_);
lean_del_object(v___x_2577_);
lean_dec_ref(v_msg_2567_);
lean_dec_ref(v_tag_2563_);
lean_dec(v_cls_2561_);
v___x_2619_ = lean_st_ref_take(v___y_2572_);
v_traceState_2620_ = lean_ctor_get(v___x_2619_, 4);
v_env_2621_ = lean_ctor_get(v___x_2619_, 0);
v_nextMacroScope_2622_ = lean_ctor_get(v___x_2619_, 1);
v_ngen_2623_ = lean_ctor_get(v___x_2619_, 2);
v_auxDeclNGen_2624_ = lean_ctor_get(v___x_2619_, 3);
v_cache_2625_ = lean_ctor_get(v___x_2619_, 5);
v_messages_2626_ = lean_ctor_get(v___x_2619_, 6);
v_infoState_2627_ = lean_ctor_get(v___x_2619_, 7);
v_snapshotTasks_2628_ = lean_ctor_get(v___x_2619_, 8);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2630_ = v___x_2619_;
v_isShared_2631_ = v_isSharedCheck_2647_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_snapshotTasks_2628_);
lean_inc(v_infoState_2627_);
lean_inc(v_messages_2626_);
lean_inc(v_cache_2625_);
lean_inc(v_traceState_2620_);
lean_inc(v_auxDeclNGen_2624_);
lean_inc(v_ngen_2623_);
lean_inc(v_nextMacroScope_2622_);
lean_inc(v_env_2621_);
lean_dec(v___x_2619_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2647_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
uint64_t v_tid_2632_; lean_object* v_traces_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2646_; 
v_tid_2632_ = lean_ctor_get_uint64(v_traceState_2620_, sizeof(void*)*1);
v_traces_2633_ = lean_ctor_get(v_traceState_2620_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_traceState_2620_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2635_ = v_traceState_2620_;
v_isShared_2636_ = v_isSharedCheck_2646_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_traces_2633_);
lean_dec(v_traceState_2620_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2646_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2637_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2566_, v_traces_2633_);
lean_dec_ref(v_traces_2633_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2637_);
v___x_2639_ = v___x_2635_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2637_);
lean_ctor_set_uint64(v_reuseFailAlloc_2645_, sizeof(void*)*1, v_tid_2632_);
v___x_2639_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2641_; 
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 4, v___x_2639_);
v___x_2641_ = v___x_2630_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_env_2621_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_nextMacroScope_2622_);
lean_ctor_set(v_reuseFailAlloc_2644_, 2, v_ngen_2623_);
lean_ctor_set(v_reuseFailAlloc_2644_, 3, v_auxDeclNGen_2624_);
lean_ctor_set(v_reuseFailAlloc_2644_, 4, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2644_, 5, v_cache_2625_);
lean_ctor_set(v_reuseFailAlloc_2644_, 6, v_messages_2626_);
lean_ctor_set(v_reuseFailAlloc_2644_, 7, v_infoState_2627_);
lean_ctor_set(v_reuseFailAlloc_2644_, 8, v_snapshotTasks_2628_);
v___x_2641_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = lean_st_ref_set(v___y_2572_, v___x_2641_);
v___x_2643_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2574_);
return v___x_2643_;
}
}
}
}
}
else
{
goto v___jp_2612_;
}
}
else
{
goto v___jp_2612_;
}
}
v___jp_2648_:
{
double v___x_2650_; double v___x_2651_; double v___x_2652_; uint8_t v___x_2653_; 
v___x_2650_ = lean_unbox_float(v_snd_2586_);
v___x_2651_ = lean_unbox_float(v_fst_2585_);
v___x_2652_ = lean_float_sub(v___x_2650_, v___x_2651_);
v___x_2653_ = lean_float_decLt(v___y_2649_, v___x_2652_);
v___y_2618_ = v___x_2653_;
goto v___jp_2617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2666_, lean_object* v_collapsed_2667_, lean_object* v_tag_2668_, lean_object* v_opts_2669_, lean_object* v_clsEnabled_2670_, lean_object* v_oldTraces_2671_, lean_object* v_msg_2672_, lean_object* v_resStartStop_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
uint8_t v_collapsed_boxed_2679_; uint8_t v_clsEnabled_boxed_2680_; lean_object* v_res_2681_; 
v_collapsed_boxed_2679_ = lean_unbox(v_collapsed_2667_);
v_clsEnabled_boxed_2680_ = lean_unbox(v_clsEnabled_2670_);
v_res_2681_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2666_, v_collapsed_boxed_2679_, v_tag_2668_, v_opts_2669_, v_clsEnabled_boxed_2680_, v_oldTraces_2671_, v_msg_2672_, v_resStartStop_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec_ref(v_opts_2669_);
return v_res_2681_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0(void){
_start:
{
lean_object* v___x_2682_; double v___x_2683_; 
v___x_2682_ = lean_unsigned_to_nat(1000000000u);
v___x_2683_ = lean_float_of_nat(v___x_2682_);
return v___x_2683_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1));
v___x_2686_ = l_Lean_stringToMessageData(v___x_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v_toConstantVal_2693_; lean_object* v_options_2694_; lean_object* v_name_2695_; lean_object* v_levelParams_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2907_; 
v_toConstantVal_2693_ = lean_ctor_get(v_ctorVal_2687_, 0);
lean_inc_ref(v_toConstantVal_2693_);
v_options_2694_ = lean_ctor_get(v_a_2690_, 2);
v_name_2695_ = lean_ctor_get(v_toConstantVal_2693_, 0);
v_levelParams_2696_ = lean_ctor_get(v_toConstantVal_2693_, 1);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_toConstantVal_2693_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; 
v_unused_2908_ = lean_ctor_get(v_toConstantVal_2693_, 2);
lean_dec(v_unused_2908_);
v___x_2698_ = v_toConstantVal_2693_;
v_isShared_2699_ = v_isSharedCheck_2907_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_levelParams_2696_);
lean_inc(v_name_2695_);
lean_dec(v_toConstantVal_2693_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2907_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v_inheritedTraceOptions_2700_; uint8_t v_hasTrace_2701_; lean_object* v_name_2702_; 
v_inheritedTraceOptions_2700_ = lean_ctor_get(v_a_2690_, 13);
v_hasTrace_2701_ = lean_ctor_get_uint8(v_options_2694_, sizeof(void*)*1);
lean_inc(v_name_2695_);
v_name_2702_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2695_);
if (v_hasTrace_2701_ == 0)
{
lean_object* v___x_2703_; 
v___x_2703_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2741_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2741_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2741_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
if (lean_obj_tag(v_a_2704_) == 1)
{
lean_object* v_val_2708_; lean_object* v___x_2709_; 
lean_del_object(v___x_2706_);
v_val_2708_ = lean_ctor_get(v_a_2704_, 0);
lean_inc_n(v_val_2708_, 2);
lean_dec_ref(v_a_2704_);
v___x_2709_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2695_, v_val_2708_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; lean_object* v_a_2712_; lean_object* v___x_2713_; lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2728_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref(v___x_2709_);
v___x_2711_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2708_, v_a_2689_);
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2710_, v_a_2689_);
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2728_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2728_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
lean_inc(v_name_2702_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 2, v_a_2712_);
lean_ctor_set(v___x_2698_, 0, v_name_2702_);
v___x_2719_ = v___x_2698_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_name_2702_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_levelParams_2696_);
lean_ctor_set(v_reuseFailAlloc_2727_, 2, v_a_2712_);
v___x_2719_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2720_ = lean_box(0);
v___x_2721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_name_2702_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2719_);
lean_ctor_set(v___x_2722_, 1, v_a_2714_);
lean_ctor_set(v___x_2722_, 2, v___x_2721_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set_tag(v___x_2716_, 2);
lean_ctor_set(v___x_2716_, 0, v___x_2722_);
v___x_2724_ = v___x_2716_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_addDecl(v___x_2724_, v_hasTrace_2701_, v_a_2690_, v_a_2691_);
return v___x_2725_;
}
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec(v_val_2708_);
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
v_a_2729_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2709_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2709_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
else
{
lean_object* v___x_2737_; lean_object* v___x_2739_; 
lean_dec(v_a_2704_);
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v___x_2737_ = lean_box(0);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2737_);
v___x_2739_ = v___x_2706_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v_a_2742_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2703_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2703_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
else
{
lean_object* v___f_2750_; lean_object* v_cls_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v_a_2758_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v_a_2770_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v_a_2775_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v_a_2786_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v_a_2801_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v_a_2806_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; 
lean_inc(v_name_2702_);
v___f_2750_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2750_, 0, v_name_2702_);
v_cls_2751_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2752_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_2753_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_2754_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2700_, v_options_2694_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = l_Lean_trace_profiler;
v___x_2850_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2694_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; 
lean_dec_ref(v___f_2750_);
v___x_2851_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2898_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2854_ = v___x_2851_;
v_isShared_2855_ = v_isSharedCheck_2898_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2851_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2898_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
if (lean_obj_tag(v_a_2852_) == 1)
{
lean_object* v_val_2856_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; 
lean_del_object(v___x_2854_);
v_val_2856_ = lean_ctor_get(v_a_2852_, 0);
lean_inc(v_val_2856_);
lean_dec_ref(v_a_2852_);
if (v___x_2754_ == 0)
{
v___y_2858_ = v_a_2688_;
v___y_2859_ = v_a_2689_;
v___y_2860_ = v_a_2690_;
v___y_2861_ = v_a_2691_;
goto v___jp_2857_;
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2890_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_2856_);
v___x_2891_ = l_Lean_MessageData_ofExpr(v_val_2856_);
v___x_2892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2751_, v___x_2892_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_dec_ref(v___x_2893_);
v___y_2858_ = v_a_2688_;
v___y_2859_ = v_a_2689_;
v___y_2860_ = v_a_2690_;
v___y_2861_ = v_a_2691_;
goto v___jp_2857_;
}
else
{
lean_dec(v_val_2856_);
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
return v___x_2893_;
}
}
v___jp_2857_:
{
lean_object* v___x_2862_; 
lean_inc(v_val_2856_);
v___x_2862_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2695_, v_val_2856_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2864_; lean_object* v_a_2865_; lean_object* v___x_2866_; lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2881_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref(v___x_2862_);
v___x_2864_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2856_, v___y_2859_);
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref(v___x_2864_);
v___x_2866_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2863_, v___y_2859_);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2881_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2881_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
lean_inc(v_name_2702_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 2, v_a_2865_);
lean_ctor_set(v___x_2698_, 0, v_name_2702_);
v___x_2872_ = v___x_2698_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_name_2702_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_levelParams_2696_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_a_2865_);
v___x_2872_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2873_ = lean_box(0);
v___x_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2874_, 0, v_name_2702_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2872_);
lean_ctor_set(v___x_2875_, 1, v_a_2867_);
lean_ctor_set(v___x_2875_, 2, v___x_2874_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set_tag(v___x_2869_, 2);
lean_ctor_set(v___x_2869_, 0, v___x_2875_);
v___x_2877_ = v___x_2869_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_addDecl(v___x_2877_, v___x_2850_, v___y_2860_, v___y_2861_);
return v___x_2878_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_val_2856_);
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
v_a_2882_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2862_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2862_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
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
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
lean_dec(v_a_2852_);
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v___x_2894_ = lean_box(0);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v___x_2894_);
v___x_2896_ = v___x_2854_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
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
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v_name_2702_);
lean_del_object(v___x_2698_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v_a_2899_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2851_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2851_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_del_object(v___x_2698_);
goto v___jp_2814_;
}
}
else
{
lean_del_object(v___x_2698_);
goto v___jp_2814_;
}
v___jp_2755_:
{
lean_object* v___x_2759_; double v___x_2760_; double v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2759_ = lean_io_get_num_heartbeats();
v___x_2760_ = lean_float_of_nat(v___y_2757_);
v___x_2761_ = lean_float_of_nat(v___x_2759_);
v___x_2762_ = lean_box_float(v___x_2760_);
v___x_2763_ = lean_box_float(v___x_2761_);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2765_, 0, v_a_2758_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2751_, v_hasTrace_2701_, v___x_2752_, v_options_2694_, v___x_2754_, v___y_2756_, v___f_2750_, v___x_2765_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
return v___x_2766_;
}
v___jp_2767_:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_a_2770_);
v___y_2756_ = v___y_2768_;
v___y_2757_ = v___y_2769_;
v_a_2758_ = v___x_2771_;
goto v___jp_2755_;
}
v___jp_2772_:
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2776_, 0, v_a_2775_);
v___y_2756_ = v___y_2773_;
v___y_2757_ = v___y_2774_;
v_a_2758_ = v___x_2776_;
goto v___jp_2755_;
}
v___jp_2777_:
{
if (lean_obj_tag(v___y_2780_) == 0)
{
lean_object* v_a_2781_; 
v_a_2781_ = lean_ctor_get(v___y_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref(v___y_2780_);
v___y_2773_ = v___y_2778_;
v___y_2774_ = v___y_2779_;
v_a_2775_ = v_a_2781_;
goto v___jp_2772_;
}
else
{
lean_object* v_a_2782_; 
v_a_2782_ = lean_ctor_get(v___y_2780_, 0);
lean_inc(v_a_2782_);
lean_dec_ref(v___y_2780_);
v___y_2768_ = v___y_2778_;
v___y_2769_ = v___y_2779_;
v_a_2770_ = v_a_2782_;
goto v___jp_2767_;
}
}
v___jp_2783_:
{
lean_object* v___x_2787_; double v___x_2788_; double v___x_2789_; double v___x_2790_; double v___x_2791_; double v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2787_ = lean_io_mono_nanos_now();
v___x_2788_ = lean_float_of_nat(v___y_2785_);
v___x_2789_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_2790_ = lean_float_div(v___x_2788_, v___x_2789_);
v___x_2791_ = lean_float_of_nat(v___x_2787_);
v___x_2792_ = lean_float_div(v___x_2791_, v___x_2789_);
v___x_2793_ = lean_box_float(v___x_2790_);
v___x_2794_ = lean_box_float(v___x_2792_);
v___x_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v_a_2786_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2751_, v_hasTrace_2701_, v___x_2752_, v_options_2694_, v___x_2754_, v___y_2784_, v___f_2750_, v___x_2796_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
return v___x_2797_;
}
v___jp_2798_:
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v_a_2801_);
v___y_2784_ = v___y_2799_;
v___y_2785_ = v___y_2800_;
v_a_2786_ = v___x_2802_;
goto v___jp_2783_;
}
v___jp_2803_:
{
lean_object* v___x_2807_; 
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v_a_2806_);
v___y_2784_ = v___y_2804_;
v___y_2785_ = v___y_2805_;
v_a_2786_ = v___x_2807_;
goto v___jp_2783_;
}
v___jp_2808_:
{
if (lean_obj_tag(v___y_2811_) == 0)
{
lean_object* v_a_2812_; 
v_a_2812_ = lean_ctor_get(v___y_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref(v___y_2811_);
v___y_2799_ = v___y_2809_;
v___y_2800_ = v___y_2810_;
v_a_2801_ = v_a_2812_;
goto v___jp_2798_;
}
else
{
lean_object* v_a_2813_; 
v_a_2813_ = lean_ctor_get(v___y_2811_, 0);
lean_inc(v_a_2813_);
lean_dec_ref(v___y_2811_);
v___y_2804_ = v___y_2809_;
v___y_2805_ = v___y_2810_;
v_a_2806_ = v_a_2813_;
goto v___jp_2803_;
}
}
v___jp_2814_:
{
lean_object* v___x_2815_; lean_object* v_a_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2815_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2691_);
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref(v___x_2815_);
v___x_2817_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2818_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2694_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_io_mono_nanos_now();
v___x_2820_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref(v___x_2820_);
if (lean_obj_tag(v_a_2821_) == 1)
{
if (v___x_2754_ == 0)
{
lean_object* v_val_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_val_2822_ = lean_ctor_get(v_a_2821_, 0);
lean_inc(v_val_2822_);
lean_dec_ref(v_a_2821_);
v___x_2823_ = lean_box(0);
v___x_2824_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2695_, v_val_2822_, v_name_2702_, v_levelParams_2696_, v___x_2818_, v___x_2823_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
v___y_2809_ = v_a_2816_;
v___y_2810_ = v___x_2819_;
v___y_2811_ = v___x_2824_;
goto v___jp_2808_;
}
else
{
lean_object* v_val_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_val_2825_ = lean_ctor_get(v_a_2821_, 0);
lean_inc_n(v_val_2825_, 2);
lean_dec_ref(v_a_2821_);
v___x_2826_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2827_ = l_Lean_MessageData_ofExpr(v_val_2825_);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2751_, v___x_2828_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2831_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref(v___x_2829_);
v___x_2831_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2695_, v_val_2825_, v_name_2702_, v_levelParams_2696_, v___x_2818_, v_a_2830_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
v___y_2809_ = v_a_2816_;
v___y_2810_ = v___x_2819_;
v___y_2811_ = v___x_2831_;
goto v___jp_2808_;
}
else
{
lean_dec(v_val_2825_);
lean_dec(v_name_2702_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v___y_2809_ = v_a_2816_;
v___y_2810_ = v___x_2819_;
v___y_2811_ = v___x_2829_;
goto v___jp_2808_;
}
}
}
else
{
lean_object* v___x_2832_; 
lean_dec(v_a_2821_);
lean_dec(v_name_2702_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v___x_2832_ = lean_box(0);
v___y_2799_ = v_a_2816_;
v___y_2800_ = v___x_2819_;
v_a_2801_ = v___x_2832_;
goto v___jp_2798_;
}
}
else
{
lean_object* v_a_2833_; 
lean_dec(v_name_2702_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v_a_2833_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2833_);
lean_dec_ref(v___x_2820_);
v___y_2804_ = v_a_2816_;
v___y_2805_ = v___x_2819_;
v_a_2806_ = v_a_2833_;
goto v___jp_2803_;
}
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_io_get_num_heartbeats();
v___x_2835_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref(v___x_2835_);
if (lean_obj_tag(v_a_2836_) == 1)
{
if (v___x_2754_ == 0)
{
lean_object* v_val_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v_val_2837_ = lean_ctor_get(v_a_2836_, 0);
lean_inc(v_val_2837_);
lean_dec_ref(v_a_2836_);
v___x_2838_ = lean_box(0);
v___x_2839_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2695_, v_val_2837_, v_name_2702_, v_levelParams_2696_, v___x_2838_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
v___y_2778_ = v_a_2816_;
v___y_2779_ = v___x_2834_;
v___y_2780_ = v___x_2839_;
goto v___jp_2777_;
}
else
{
lean_object* v_val_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v_val_2840_ = lean_ctor_get(v_a_2836_, 0);
lean_inc_n(v_val_2840_, 2);
lean_dec_ref(v_a_2836_);
v___x_2841_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2842_ = l_Lean_MessageData_ofExpr(v_val_2840_);
v___x_2843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_2751_, v___x_2843_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref(v___x_2844_);
v___x_2846_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2695_, v_val_2840_, v_name_2702_, v_levelParams_2696_, v_a_2845_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
v___y_2778_ = v_a_2816_;
v___y_2779_ = v___x_2834_;
v___y_2780_ = v___x_2846_;
goto v___jp_2777_;
}
else
{
lean_dec(v_val_2840_);
lean_dec(v_name_2702_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v___y_2778_ = v_a_2816_;
v___y_2779_ = v___x_2834_;
v___y_2780_ = v___x_2844_;
goto v___jp_2777_;
}
}
}
else
{
lean_object* v___x_2847_; 
lean_dec(v_a_2836_);
lean_dec(v_name_2702_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v___x_2847_ = lean_box(0);
v___y_2773_ = v_a_2816_;
v___y_2774_ = v___x_2834_;
v_a_2775_ = v___x_2847_;
goto v___jp_2772_;
}
}
else
{
lean_object* v_a_2848_; 
lean_dec(v_name_2702_);
lean_dec(v_levelParams_2696_);
lean_dec(v_name_2695_);
v_a_2848_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2848_);
lean_dec_ref(v___x_2835_);
v___y_2768_ = v_a_2816_;
v___y_2769_ = v___x_2834_;
v_a_2770_ = v_a_2848_;
goto v___jp_2767_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_00_u03b1_2916_, lean_object* v_x_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2917_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2924_, lean_object* v_x_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_00_u03b1_2924_, v_x_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2935_){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2937_ = l_Lean_Name_append(v_ctorName_2935_, v___x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
uint8_t v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = 1;
v___x_2945_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2938_, v___x_2944_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2953_, lean_object* v_t_2954_, lean_object* v_acc_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2954_, v_a_2956_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2982_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2982_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2982_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = l_Lean_Expr_cleanupAnnotations(v_a_2959_);
v___x_2969_ = l_Lean_Expr_isApp(v___x_2968_);
if (v___x_2969_ == 0)
{
lean_dec_ref(v___x_2968_);
goto v___jp_2963_;
}
else
{
lean_object* v_arg_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_arg_2970_ = lean_ctor_get(v___x_2968_, 1);
lean_inc_ref(v_arg_2970_);
v___x_2971_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2968_);
v___x_2972_ = l_Lean_Expr_isApp(v___x_2971_);
if (v___x_2972_ == 0)
{
lean_dec_ref(v___x_2971_);
lean_dec_ref(v_arg_2970_);
goto v___jp_2963_;
}
else
{
lean_object* v_arg_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; 
v_arg_2973_ = lean_ctor_get(v___x_2971_, 1);
lean_inc_ref(v_arg_2973_);
v___x_2974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2971_);
v___x_2975_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_2976_ = l_Lean_Expr_isConstOf(v___x_2974_, v___x_2975_);
lean_dec_ref(v___x_2974_);
if (v___x_2976_ == 0)
{
lean_dec_ref(v_arg_2973_);
lean_dec_ref(v_arg_2970_);
goto v___jp_2963_;
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_del_object(v___x_2961_);
v___x_2977_ = lean_unsigned_to_nat(0u);
v___x_2978_ = l_Lean_mkProj(v___x_2975_, v___x_2977_, v_e_2953_);
lean_inc_ref(v___x_2978_);
v___x_2979_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_2978_, v_arg_2973_, v_acc_2955_, v_a_2956_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref(v___x_2979_);
v_e_2953_ = v___x_2978_;
v_t_2954_ = v_arg_2970_;
v_acc_2955_ = v_a_2980_;
goto _start;
}
else
{
lean_dec_ref(v___x_2978_);
lean_dec_ref(v_arg_2970_);
return v___x_2979_;
}
}
}
}
v___jp_2963_:
{
lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2964_ = lean_array_push(v_acc_2955_, v_e_2953_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2964_);
v___x_2966_ = v___x_2961_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v_acc_2955_);
lean_dec_ref(v_e_2953_);
v_a_2983_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2958_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2958_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_2991_, lean_object* v_t_2992_, lean_object* v_acc_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2991_, v_t_2992_, v_acc_2993_, v_a_2994_);
lean_dec(v_a_2994_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_2997_, lean_object* v_t_2998_, lean_object* v_acc_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_2997_, v_t_2998_, v_acc_2999_, v_a_3001_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_3006_, lean_object* v_t_3007_, lean_object* v_acc_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_3006_, v_t_3007_, v_acc_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v___x_3021_; 
lean_inc(v_a_3019_);
lean_inc_ref(v_a_3018_);
lean_inc(v_a_3017_);
lean_inc_ref(v_a_3016_);
lean_inc_ref(v_e_3015_);
v___x_3021_ = lean_infer_type(v_e_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref(v___x_3021_);
v___x_3023_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3024_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3015_, v_a_3022_, v___x_3023_, v_a_3017_);
return v___x_3024_;
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v_e_3015_);
v_a_3025_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3021_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3021_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec_ref(v_a_3034_);
return v_res_3039_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = lean_box(0);
v___x_3046_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2));
v___x_3047_ = l_Lean_mkConst(v___x_3046_, v___x_3045_);
return v___x_3047_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__4));
v___x_3050_ = l_Lean_stringToMessageData(v___x_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_b_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___x_3057_; 
lean_inc(v_b_3051_);
v___x_3057_ = l_Lean_MVarId_getType(v_b_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3138_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3138_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3138_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
if (lean_obj_tag(v_a_3058_) == 7)
{
lean_object* v_binderType_3062_; lean_object* v_body_3063_; uint8_t v___x_3064_; lean_object* v_mvarId_u2082_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; 
v_binderType_3062_ = lean_ctor_get(v_a_3058_, 1);
lean_inc_ref(v_binderType_3062_);
v_body_3063_ = lean_ctor_get(v_a_3058_, 2);
lean_inc_ref(v_body_3063_);
lean_dec_ref(v_a_3058_);
v___x_3064_ = l_Lean_Expr_hasLooseBVars(v_body_3063_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3083_; 
lean_del_object(v___x_3060_);
v___x_3083_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3062_, v___y_3053_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref(v___x_3083_);
v___x_3085_ = l_Lean_Expr_cleanupAnnotations(v_a_3084_);
v___x_3086_ = l_Lean_Expr_isApp(v___x_3085_);
if (v___x_3086_ == 0)
{
lean_dec_ref(v___x_3085_);
lean_dec_ref(v_body_3063_);
v_mvarId_u2082_3066_ = v_b_3051_;
v___y_3067_ = v___y_3052_;
v___y_3068_ = v___y_3053_;
v___y_3069_ = v___y_3054_;
v___y_3070_ = v___y_3055_;
goto v___jp_3065_;
}
else
{
lean_object* v_arg_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v_arg_3087_ = lean_ctor_get(v___x_3085_, 1);
lean_inc_ref(v_arg_3087_);
v___x_3088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3085_);
v___x_3089_ = l_Lean_Expr_isApp(v___x_3088_);
if (v___x_3089_ == 0)
{
lean_dec_ref(v___x_3088_);
lean_dec_ref(v_arg_3087_);
lean_dec_ref(v_body_3063_);
v_mvarId_u2082_3066_ = v_b_3051_;
v___y_3067_ = v___y_3052_;
v___y_3068_ = v___y_3053_;
v___y_3069_ = v___y_3054_;
v___y_3070_ = v___y_3055_;
goto v___jp_3065_;
}
else
{
lean_object* v_arg_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; 
v_arg_3090_ = lean_ctor_get(v___x_3088_, 1);
lean_inc_ref(v_arg_3090_);
v___x_3091_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3088_);
v___x_3092_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3093_ = l_Lean_Expr_isConstOf(v___x_3091_, v___x_3092_);
lean_dec_ref(v___x_3091_);
if (v___x_3093_ == 0)
{
lean_dec_ref(v_arg_3090_);
lean_dec_ref(v_arg_3087_);
lean_dec_ref(v_body_3063_);
v_mvarId_u2082_3066_ = v_b_3051_;
v___y_3067_ = v___y_3052_;
v___y_3068_ = v___y_3053_;
v___y_3069_ = v___y_3054_;
v___y_3070_ = v___y_3055_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3094_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3);
v___x_3095_ = l_Lean_mkApp3(v___x_3094_, v_arg_3090_, v_arg_3087_, v_body_3063_);
v___x_3096_ = lean_unsigned_to_nat(1u);
lean_inc(v_b_3051_);
v___x_3097_ = l_Lean_MVarId_applyN(v_b_3051_, v___x_3095_, v___x_3096_, v___x_3093_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref(v___x_3097_);
if (lean_obj_tag(v_a_3098_) == 1)
{
lean_object* v_tail_3114_; 
v_tail_3114_ = lean_ctor_get(v_a_3098_, 1);
if (lean_obj_tag(v_tail_3114_) == 0)
{
lean_object* v_head_3115_; 
lean_dec(v_b_3051_);
v_head_3115_ = lean_ctor_get(v_a_3098_, 0);
lean_inc(v_head_3115_);
lean_dec_ref(v_a_3098_);
v_mvarId_u2082_3066_ = v_head_3115_;
v___y_3067_ = v___y_3052_;
v___y_3068_ = v___y_3053_;
v___y_3069_ = v___y_3054_;
v___y_3070_ = v___y_3055_;
goto v___jp_3065_;
}
else
{
lean_dec_ref(v_a_3098_);
v___y_3100_ = v___y_3052_;
v___y_3101_ = v___y_3053_;
v___y_3102_ = v___y_3054_;
v___y_3103_ = v___y_3055_;
goto v___jp_3099_;
}
}
else
{
lean_dec(v_a_3098_);
v___y_3100_ = v___y_3052_;
v___y_3101_ = v___y_3053_;
v___y_3102_ = v___y_3054_;
v___y_3103_ = v___y_3055_;
goto v___jp_3099_;
}
v___jp_3099_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5);
v___x_3105_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3104_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_dec_ref(v___x_3105_);
v_mvarId_u2082_3066_ = v_b_3051_;
v___y_3067_ = v___y_3100_;
v___y_3068_ = v___y_3101_;
v___y_3069_ = v___y_3102_;
v___y_3070_ = v___y_3103_;
goto v___jp_3065_;
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec(v_b_3051_);
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3105_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3105_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec(v_b_3051_);
v_a_3116_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3097_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3097_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec_ref(v_body_3063_);
lean_dec(v_b_3051_);
v_a_3124_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3083_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3083_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
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
lean_object* v___x_3133_; 
lean_dec_ref(v_body_3063_);
lean_dec_ref(v_binderType_3062_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v_b_3051_);
v___x_3133_ = v___x_3060_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_b_3051_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
v___jp_3065_:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3066_, v___x_3064_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v_snd_3073_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref(v___x_3071_);
v_snd_3073_ = lean_ctor_get(v_a_3072_, 1);
lean_inc(v_snd_3073_);
lean_dec(v_a_3072_);
v_b_3051_ = v_snd_3073_;
goto _start;
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
v_a_3075_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3071_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3071_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
else
{
lean_object* v___x_3136_; 
lean_dec(v_a_3058_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v_b_3051_);
v___x_3136_ = v___x_3060_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_b_3051_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v_b_3051_);
v_a_3139_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3057_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3057_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_b_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_b_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3154_, lean_object* v_x_3155_, lean_object* v_x_3156_, lean_object* v_x_3157_){
_start:
{
lean_object* v_ks_3158_; lean_object* v_vs_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3183_; 
v_ks_3158_ = lean_ctor_get(v_x_3154_, 0);
v_vs_3159_ = lean_ctor_get(v_x_3154_, 1);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_x_3154_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3161_ = v_x_3154_;
v_isShared_3162_ = v_isSharedCheck_3183_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_vs_3159_);
lean_inc(v_ks_3158_);
lean_dec(v_x_3154_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3183_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; uint8_t v___x_3164_; 
v___x_3163_ = lean_array_get_size(v_ks_3158_);
v___x_3164_ = lean_nat_dec_lt(v_x_3155_, v___x_3163_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; 
lean_dec(v_x_3155_);
v___x_3165_ = lean_array_push(v_ks_3158_, v_x_3156_);
v___x_3166_ = lean_array_push(v_vs_3159_, v_x_3157_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 1, v___x_3166_);
lean_ctor_set(v___x_3161_, 0, v___x_3165_);
v___x_3168_ = v___x_3161_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
else
{
lean_object* v_k_x27_3170_; uint8_t v___x_3171_; 
v_k_x27_3170_ = lean_array_fget_borrowed(v_ks_3158_, v_x_3155_);
v___x_3171_ = l_Lean_instBEqMVarId_beq(v_x_3156_, v_k_x27_3170_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3173_; 
if (v_isShared_3162_ == 0)
{
v___x_3173_ = v___x_3161_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_ks_3158_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_vs_3159_);
v___x_3173_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = lean_unsigned_to_nat(1u);
v___x_3175_ = lean_nat_add(v_x_3155_, v___x_3174_);
lean_dec(v_x_3155_);
v_x_3154_ = v___x_3173_;
v_x_3155_ = v___x_3175_;
goto _start;
}
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3178_ = lean_array_fset(v_ks_3158_, v_x_3155_, v_x_3156_);
v___x_3179_ = lean_array_fset(v_vs_3159_, v_x_3155_, v_x_3157_);
lean_dec(v_x_3155_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 1, v___x_3179_);
lean_ctor_set(v___x_3161_, 0, v___x_3178_);
v___x_3181_ = v___x_3161_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3184_, lean_object* v_k_3185_, lean_object* v_v_3186_){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_unsigned_to_nat(0u);
v___x_3188_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3184_, v___x_3187_, v_k_3185_, v_v_3186_);
return v___x_3188_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_3189_; size_t v___x_3190_; size_t v___x_3191_; 
v___x_3189_ = ((size_t)5ULL);
v___x_3190_ = ((size_t)1ULL);
v___x_3191_ = lean_usize_shift_left(v___x_3190_, v___x_3189_);
return v___x_3191_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_3192_; size_t v___x_3193_; size_t v___x_3194_; 
v___x_3192_ = ((size_t)1ULL);
v___x_3193_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3194_ = lean_usize_sub(v___x_3193_, v___x_3192_);
return v___x_3194_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3196_, size_t v_x_3197_, size_t v_x_3198_, lean_object* v_x_3199_, lean_object* v_x_3200_){
_start:
{
if (lean_obj_tag(v_x_3196_) == 0)
{
lean_object* v_es_3201_; size_t v___x_3202_; size_t v___x_3203_; size_t v___x_3204_; size_t v___x_3205_; lean_object* v_j_3206_; lean_object* v___x_3207_; uint8_t v___x_3208_; 
v_es_3201_ = lean_ctor_get(v_x_3196_, 0);
v___x_3202_ = ((size_t)5ULL);
v___x_3203_ = ((size_t)1ULL);
v___x_3204_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3205_ = lean_usize_land(v_x_3197_, v___x_3204_);
v_j_3206_ = lean_usize_to_nat(v___x_3205_);
v___x_3207_ = lean_array_get_size(v_es_3201_);
v___x_3208_ = lean_nat_dec_lt(v_j_3206_, v___x_3207_);
if (v___x_3208_ == 0)
{
lean_dec(v_j_3206_);
lean_dec(v_x_3200_);
lean_dec(v_x_3199_);
return v_x_3196_;
}
else
{
lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3245_; 
lean_inc_ref(v_es_3201_);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_x_3196_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; 
v_unused_3246_ = lean_ctor_get(v_x_3196_, 0);
lean_dec(v_unused_3246_);
v___x_3210_ = v_x_3196_;
v_isShared_3211_ = v_isSharedCheck_3245_;
goto v_resetjp_3209_;
}
else
{
lean_dec(v_x_3196_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3245_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v_v_3212_; lean_object* v___x_3213_; lean_object* v_xs_x27_3214_; lean_object* v___y_3216_; 
v_v_3212_ = lean_array_fget(v_es_3201_, v_j_3206_);
v___x_3213_ = lean_box(0);
v_xs_x27_3214_ = lean_array_fset(v_es_3201_, v_j_3206_, v___x_3213_);
switch(lean_obj_tag(v_v_3212_))
{
case 0:
{
lean_object* v_key_3221_; lean_object* v_val_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3232_; 
v_key_3221_ = lean_ctor_get(v_v_3212_, 0);
v_val_3222_ = lean_ctor_get(v_v_3212_, 1);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_v_3212_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3224_ = v_v_3212_;
v_isShared_3225_ = v_isSharedCheck_3232_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_val_3222_);
lean_inc(v_key_3221_);
lean_dec(v_v_3212_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3232_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
uint8_t v___x_3226_; 
v___x_3226_ = l_Lean_instBEqMVarId_beq(v_x_3199_, v_key_3221_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
lean_del_object(v___x_3224_);
v___x_3227_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3221_, v_val_3222_, v_x_3199_, v_x_3200_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
v___y_3216_ = v___x_3228_;
goto v___jp_3215_;
}
else
{
lean_object* v___x_3230_; 
lean_dec(v_val_3222_);
lean_dec(v_key_3221_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 1, v_x_3200_);
lean_ctor_set(v___x_3224_, 0, v_x_3199_);
v___x_3230_ = v___x_3224_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_x_3199_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_x_3200_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
v___y_3216_ = v___x_3230_;
goto v___jp_3215_;
}
}
}
}
case 1:
{
lean_object* v_node_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3243_; 
v_node_3233_ = lean_ctor_get(v_v_3212_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_v_3212_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3235_ = v_v_3212_;
v_isShared_3236_ = v_isSharedCheck_3243_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_node_3233_);
lean_dec(v_v_3212_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3243_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
size_t v___x_3237_; size_t v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3237_ = lean_usize_shift_right(v_x_3197_, v___x_3202_);
v___x_3238_ = lean_usize_add(v_x_3198_, v___x_3203_);
v___x_3239_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3233_, v___x_3237_, v___x_3238_, v_x_3199_, v_x_3200_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3239_);
v___x_3241_ = v___x_3235_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
v___y_3216_ = v___x_3241_;
goto v___jp_3215_;
}
}
}
default: 
{
lean_object* v___x_3244_; 
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v_x_3199_);
lean_ctor_set(v___x_3244_, 1, v_x_3200_);
v___y_3216_ = v___x_3244_;
goto v___jp_3215_;
}
}
v___jp_3215_:
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3217_ = lean_array_fset(v_xs_x27_3214_, v_j_3206_, v___y_3216_);
lean_dec(v_j_3206_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3217_);
v___x_3219_ = v___x_3210_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
else
{
lean_object* v_ks_3247_; lean_object* v_vs_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3268_; 
v_ks_3247_ = lean_ctor_get(v_x_3196_, 0);
v_vs_3248_ = lean_ctor_get(v_x_3196_, 1);
v_isSharedCheck_3268_ = !lean_is_exclusive(v_x_3196_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3250_ = v_x_3196_;
v_isShared_3251_ = v_isSharedCheck_3268_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_vs_3248_);
lean_inc(v_ks_3247_);
lean_dec(v_x_3196_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3268_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_ks_3247_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_vs_3248_);
v___x_3253_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v_newNode_3254_; uint8_t v___y_3256_; size_t v___x_3262_; uint8_t v___x_3263_; 
v_newNode_3254_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3253_, v_x_3199_, v_x_3200_);
v___x_3262_ = ((size_t)7ULL);
v___x_3263_ = lean_usize_dec_le(v___x_3262_, v_x_3198_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v___x_3264_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3254_);
v___x_3265_ = lean_unsigned_to_nat(4u);
v___x_3266_ = lean_nat_dec_lt(v___x_3264_, v___x_3265_);
lean_dec(v___x_3264_);
v___y_3256_ = v___x_3266_;
goto v___jp_3255_;
}
else
{
v___y_3256_ = v___x_3263_;
goto v___jp_3255_;
}
v___jp_3255_:
{
if (v___y_3256_ == 0)
{
lean_object* v_ks_3257_; lean_object* v_vs_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v_ks_3257_ = lean_ctor_get(v_newNode_3254_, 0);
lean_inc_ref(v_ks_3257_);
v_vs_3258_ = lean_ctor_get(v_newNode_3254_, 1);
lean_inc_ref(v_vs_3258_);
lean_dec_ref(v_newNode_3254_);
v___x_3259_ = lean_unsigned_to_nat(0u);
v___x_3260_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_3261_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3198_, v_ks_3257_, v_vs_3258_, v___x_3259_, v___x_3260_);
lean_dec_ref(v_vs_3258_);
lean_dec_ref(v_ks_3257_);
return v___x_3261_;
}
else
{
return v_newNode_3254_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3269_, lean_object* v_keys_3270_, lean_object* v_vals_3271_, lean_object* v_i_3272_, lean_object* v_entries_3273_){
_start:
{
lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3274_ = lean_array_get_size(v_keys_3270_);
v___x_3275_ = lean_nat_dec_lt(v_i_3272_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_dec(v_i_3272_);
return v_entries_3273_;
}
else
{
lean_object* v_k_3276_; lean_object* v_v_3277_; uint64_t v___x_3278_; size_t v_h_3279_; size_t v___x_3280_; lean_object* v___x_3281_; size_t v___x_3282_; size_t v___x_3283_; size_t v___x_3284_; size_t v_h_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_k_3276_ = lean_array_fget_borrowed(v_keys_3270_, v_i_3272_);
v_v_3277_ = lean_array_fget_borrowed(v_vals_3271_, v_i_3272_);
v___x_3278_ = l_Lean_instHashableMVarId_hash(v_k_3276_);
v_h_3279_ = lean_uint64_to_usize(v___x_3278_);
v___x_3280_ = ((size_t)5ULL);
v___x_3281_ = lean_unsigned_to_nat(1u);
v___x_3282_ = ((size_t)1ULL);
v___x_3283_ = lean_usize_sub(v_depth_3269_, v___x_3282_);
v___x_3284_ = lean_usize_mul(v___x_3280_, v___x_3283_);
v_h_3285_ = lean_usize_shift_right(v_h_3279_, v___x_3284_);
v___x_3286_ = lean_nat_add(v_i_3272_, v___x_3281_);
lean_dec(v_i_3272_);
lean_inc(v_v_3277_);
lean_inc(v_k_3276_);
v___x_3287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3273_, v_h_3285_, v_depth_3269_, v_k_3276_, v_v_3277_);
v_i_3272_ = v___x_3286_;
v_entries_3273_ = v___x_3287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3289_, lean_object* v_keys_3290_, lean_object* v_vals_3291_, lean_object* v_i_3292_, lean_object* v_entries_3293_){
_start:
{
size_t v_depth_boxed_3294_; lean_object* v_res_3295_; 
v_depth_boxed_3294_ = lean_unbox_usize(v_depth_3289_);
lean_dec(v_depth_3289_);
v_res_3295_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3294_, v_keys_3290_, v_vals_3291_, v_i_3292_, v_entries_3293_);
lean_dec_ref(v_vals_3291_);
lean_dec_ref(v_keys_3290_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3296_, lean_object* v_x_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_){
_start:
{
size_t v_x_5084__boxed_3301_; size_t v_x_5085__boxed_3302_; lean_object* v_res_3303_; 
v_x_5084__boxed_3301_ = lean_unbox_usize(v_x_3297_);
lean_dec(v_x_3297_);
v_x_5085__boxed_3302_ = lean_unbox_usize(v_x_3298_);
lean_dec(v_x_3298_);
v_res_3303_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3296_, v_x_5084__boxed_3301_, v_x_5085__boxed_3302_, v_x_3299_, v_x_3300_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3304_, lean_object* v_x_3305_, lean_object* v_x_3306_){
_start:
{
uint64_t v___x_3307_; size_t v___x_3308_; size_t v___x_3309_; lean_object* v___x_3310_; 
v___x_3307_ = l_Lean_instHashableMVarId_hash(v_x_3305_);
v___x_3308_ = lean_uint64_to_usize(v___x_3307_);
v___x_3309_ = ((size_t)1ULL);
v___x_3310_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3304_, v___x_3308_, v___x_3309_, v_x_3305_, v_x_3306_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3311_, lean_object* v_val_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v___x_3315_; lean_object* v_mctx_3316_; lean_object* v_cache_3317_; lean_object* v_zetaDeltaFVarIds_3318_; lean_object* v_postponed_3319_; lean_object* v_diag_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3348_; 
v___x_3315_ = lean_st_ref_take(v___y_3313_);
v_mctx_3316_ = lean_ctor_get(v___x_3315_, 0);
v_cache_3317_ = lean_ctor_get(v___x_3315_, 1);
v_zetaDeltaFVarIds_3318_ = lean_ctor_get(v___x_3315_, 2);
v_postponed_3319_ = lean_ctor_get(v___x_3315_, 3);
v_diag_3320_ = lean_ctor_get(v___x_3315_, 4);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3322_ = v___x_3315_;
v_isShared_3323_ = v_isSharedCheck_3348_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_diag_3320_);
lean_inc(v_postponed_3319_);
lean_inc(v_zetaDeltaFVarIds_3318_);
lean_inc(v_cache_3317_);
lean_inc(v_mctx_3316_);
lean_dec(v___x_3315_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3348_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v_depth_3324_; lean_object* v_levelAssignDepth_3325_; lean_object* v_lmvarCounter_3326_; lean_object* v_mvarCounter_3327_; lean_object* v_lDecls_3328_; lean_object* v_decls_3329_; lean_object* v_userNames_3330_; lean_object* v_lAssignment_3331_; lean_object* v_eAssignment_3332_; lean_object* v_dAssignment_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3347_; 
v_depth_3324_ = lean_ctor_get(v_mctx_3316_, 0);
v_levelAssignDepth_3325_ = lean_ctor_get(v_mctx_3316_, 1);
v_lmvarCounter_3326_ = lean_ctor_get(v_mctx_3316_, 2);
v_mvarCounter_3327_ = lean_ctor_get(v_mctx_3316_, 3);
v_lDecls_3328_ = lean_ctor_get(v_mctx_3316_, 4);
v_decls_3329_ = lean_ctor_get(v_mctx_3316_, 5);
v_userNames_3330_ = lean_ctor_get(v_mctx_3316_, 6);
v_lAssignment_3331_ = lean_ctor_get(v_mctx_3316_, 7);
v_eAssignment_3332_ = lean_ctor_get(v_mctx_3316_, 8);
v_dAssignment_3333_ = lean_ctor_get(v_mctx_3316_, 9);
v_isSharedCheck_3347_ = !lean_is_exclusive(v_mctx_3316_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3335_ = v_mctx_3316_;
v_isShared_3336_ = v_isSharedCheck_3347_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_dAssignment_3333_);
lean_inc(v_eAssignment_3332_);
lean_inc(v_lAssignment_3331_);
lean_inc(v_userNames_3330_);
lean_inc(v_decls_3329_);
lean_inc(v_lDecls_3328_);
lean_inc(v_mvarCounter_3327_);
lean_inc(v_lmvarCounter_3326_);
lean_inc(v_levelAssignDepth_3325_);
lean_inc(v_depth_3324_);
lean_dec(v_mctx_3316_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3347_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3337_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3332_, v_mvarId_3311_, v_val_3312_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 8, v___x_3337_);
v___x_3339_ = v___x_3335_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_depth_3324_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_levelAssignDepth_3325_);
lean_ctor_set(v_reuseFailAlloc_3346_, 2, v_lmvarCounter_3326_);
lean_ctor_set(v_reuseFailAlloc_3346_, 3, v_mvarCounter_3327_);
lean_ctor_set(v_reuseFailAlloc_3346_, 4, v_lDecls_3328_);
lean_ctor_set(v_reuseFailAlloc_3346_, 5, v_decls_3329_);
lean_ctor_set(v_reuseFailAlloc_3346_, 6, v_userNames_3330_);
lean_ctor_set(v_reuseFailAlloc_3346_, 7, v_lAssignment_3331_);
lean_ctor_set(v_reuseFailAlloc_3346_, 8, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3346_, 9, v_dAssignment_3333_);
v___x_3339_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
lean_object* v___x_3341_; 
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v___x_3339_);
v___x_3341_ = v___x_3322_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_cache_3317_);
lean_ctor_set(v_reuseFailAlloc_3345_, 2, v_zetaDeltaFVarIds_3318_);
lean_ctor_set(v_reuseFailAlloc_3345_, 3, v_postponed_3319_);
lean_ctor_set(v_reuseFailAlloc_3345_, 4, v_diag_3320_);
v___x_3341_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = lean_st_ref_set(v___y_3313_, v___x_3341_);
v___x_3343_ = lean_box(0);
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
return v___x_3344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3349_, lean_object* v_val_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3349_, v_val_3350_, v___y_3351_);
lean_dec(v___y_3351_);
return v_res_3353_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = lean_box(0);
v___x_3360_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3361_ = l_Lean_mkConst(v___x_3360_, v___x_3359_);
return v___x_3361_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3368_ = l_Lean_stringToMessageData(v___x_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3369_, lean_object* v_xs_3370_, lean_object* v_type_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = lean_box(0);
v___x_3378_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3371_, v___x_3377_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; uint8_t v___x_3384_; lean_object* v___y_3386_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref(v___x_3378_);
v___x_3380_ = l_Lean_Expr_mvarId_x21(v_a_3379_);
v___x_3381_ = lean_box(0);
v___x_3382_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3383_ = 1;
v___x_3384_ = 0;
v___x_3397_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3398_ = lean_box(0);
v___x_3399_ = l_Lean_MVarId_apply(v___x_3380_, v___x_3382_, v___x_3397_, v___x_3398_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref(v___x_3399_);
if (lean_obj_tag(v_a_3400_) == 1)
{
lean_object* v_tail_3414_; 
v_tail_3414_ = lean_ctor_get(v_a_3400_, 1);
lean_inc(v_tail_3414_);
if (lean_obj_tag(v_tail_3414_) == 1)
{
lean_object* v_tail_3415_; 
v_tail_3415_ = lean_ctor_get(v_tail_3414_, 1);
if (lean_obj_tag(v_tail_3415_) == 0)
{
lean_object* v_toConstantVal_3416_; lean_object* v_head_3417_; lean_object* v_head_3418_; lean_object* v_name_3419_; lean_object* v_levelParams_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_toConstantVal_3416_ = lean_ctor_get(v_ctorVal_3369_, 0);
lean_inc_ref(v_toConstantVal_3416_);
lean_dec_ref(v_ctorVal_3369_);
v_head_3417_ = lean_ctor_get(v_a_3400_, 0);
lean_inc(v_head_3417_);
lean_dec_ref(v_a_3400_);
v_head_3418_ = lean_ctor_get(v_tail_3414_, 0);
lean_inc(v_head_3418_);
lean_dec_ref(v_tail_3414_);
v_name_3419_ = lean_ctor_get(v_toConstantVal_3416_, 0);
lean_inc_n(v_name_3419_, 2);
v_levelParams_3420_ = lean_ctor_get(v_toConstantVal_3416_, 1);
lean_inc(v_levelParams_3420_);
lean_dec_ref(v_toConstantVal_3416_);
v___x_3421_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3419_);
v___x_3422_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3420_, v___x_3381_);
v___x_3423_ = l_Lean_mkConst(v___x_3421_, v___x_3422_);
v___x_3424_ = l_Lean_mkAppN(v___x_3423_, v_xs_3370_);
v___x_3425_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3417_, v___x_3424_, v___y_3373_);
lean_dec_ref(v___x_3425_);
v___x_3426_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_head_3418_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3428_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref(v___x_3426_);
v___x_3428_ = l_Lean_MVarId_refl(v_a_3427_, v___x_3383_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_dec(v_name_3419_);
v___y_3386_ = v___x_3428_;
goto v___jp_3385_;
}
else
{
lean_object* v_a_3429_; uint8_t v___y_3431_; uint8_t v___x_3434_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
v___x_3434_ = l_Lean_Exception_isInterrupt(v_a_3429_);
if (v___x_3434_ == 0)
{
uint8_t v___x_3435_; 
v___x_3435_ = l_Lean_Exception_isRuntime(v_a_3429_);
v___y_3431_ = v___x_3435_;
goto v___jp_3430_;
}
else
{
lean_dec(v_a_3429_);
v___y_3431_ = v___x_3434_;
goto v___jp_3430_;
}
v___jp_3430_:
{
if (v___y_3431_ == 0)
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
lean_dec_ref(v___x_3428_);
v___x_3432_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3419_);
v___x_3433_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3432_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
v___y_3386_ = v___x_3433_;
goto v___jp_3385_;
}
else
{
lean_dec(v_name_3419_);
v___y_3386_ = v___x_3428_;
goto v___jp_3385_;
}
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v_name_3419_);
lean_dec(v_a_3379_);
v_a_3436_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3426_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3426_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
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
lean_dec_ref(v_tail_3414_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3379_);
v___y_3402_ = v___y_3372_;
v___y_3403_ = v___y_3373_;
v___y_3404_ = v___y_3374_;
v___y_3405_ = v___y_3375_;
goto v___jp_3401_;
}
}
else
{
lean_dec(v_tail_3414_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3379_);
v___y_3402_ = v___y_3372_;
v___y_3403_ = v___y_3373_;
v___y_3404_ = v___y_3374_;
v___y_3405_ = v___y_3375_;
goto v___jp_3401_;
}
}
else
{
lean_dec(v_a_3400_);
lean_dec(v_a_3379_);
v___y_3402_ = v___y_3372_;
v___y_3403_ = v___y_3373_;
v___y_3404_ = v___y_3374_;
v___y_3405_ = v___y_3375_;
goto v___jp_3401_;
}
v___jp_3401_:
{
lean_object* v_toConstantVal_3406_; lean_object* v_name_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v_toConstantVal_3406_ = lean_ctor_get(v_ctorVal_3369_, 0);
lean_inc_ref(v_toConstantVal_3406_);
lean_dec_ref(v_ctorVal_3369_);
v_name_3407_ = lean_ctor_get(v_toConstantVal_3406_, 0);
lean_inc(v_name_3407_);
lean_dec_ref(v_toConstantVal_3406_);
v___x_3408_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3409_ = l_Lean_MessageData_ofName(v_name_3407_);
v___x_3410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3408_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3410_);
lean_ctor_set(v___x_3412_, 1, v___x_3411_);
v___x_3413_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3412_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
return v___x_3413_;
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec(v_a_3379_);
lean_dec_ref(v_ctorVal_3369_);
v_a_3444_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3399_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3399_);
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
v___jp_3385_:
{
if (lean_obj_tag(v___y_3386_) == 0)
{
uint8_t v___x_3387_; lean_object* v___x_3388_; 
lean_dec_ref(v___y_3386_);
v___x_3387_ = 1;
v___x_3388_ = l_Lean_Meta_mkLambdaFVars(v_xs_3370_, v_a_3379_, v___x_3384_, v___x_3383_, v___x_3384_, v___x_3383_, v___x_3387_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
return v___x_3388_;
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec(v_a_3379_);
v_a_3389_ = lean_ctor_get(v___y_3386_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___y_3386_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___y_3386_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___y_3386_);
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
else
{
lean_dec_ref(v_ctorVal_3369_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3452_, lean_object* v_xs_3453_, lean_object* v_type_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3452_, v_xs_3453_, v_type_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec_ref(v_xs_3453_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3461_, lean_object* v_targetType_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v___f_3468_; uint8_t v___x_3469_; lean_object* v___x_3470_; 
v___f_3468_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3468_, 0, v_ctorVal_3461_);
v___x_3469_ = 0;
v___x_3470_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3462_, v___f_3468_, v___x_3469_, v___x_3469_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3471_, lean_object* v_targetType_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3471_, v_targetType_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3479_, lean_object* v_val_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3479_, v_val_3480_, v___y_3482_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3487_, lean_object* v_val_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3487_, v_val_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3495_, lean_object* v_x_3496_, lean_object* v_x_3497_, lean_object* v_x_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3496_, v_x_3497_, v_x_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3500_, lean_object* v_x_3501_, size_t v_x_3502_, size_t v_x_3503_, lean_object* v_x_3504_, lean_object* v_x_3505_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3501_, v_x_3502_, v_x_3503_, v_x_3504_, v_x_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3507_, lean_object* v_x_3508_, lean_object* v_x_3509_, lean_object* v_x_3510_, lean_object* v_x_3511_, lean_object* v_x_3512_){
_start:
{
size_t v_x_5548__boxed_3513_; size_t v_x_5549__boxed_3514_; lean_object* v_res_3515_; 
v_x_5548__boxed_3513_ = lean_unbox_usize(v_x_3509_);
lean_dec(v_x_3509_);
v_x_5549__boxed_3514_ = lean_unbox_usize(v_x_3510_);
lean_dec(v_x_3510_);
v_res_3515_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3507_, v_x_3508_, v_x_5548__boxed_3513_, v_x_5549__boxed_3514_, v_x_3511_, v_x_3512_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3516_, lean_object* v_n_3517_, lean_object* v_k_3518_, lean_object* v_v_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3517_, v_k_3518_, v_v_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3521_, size_t v_depth_3522_, lean_object* v_keys_3523_, lean_object* v_vals_3524_, lean_object* v_heq_3525_, lean_object* v_i_3526_, lean_object* v_entries_3527_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3522_, v_keys_3523_, v_vals_3524_, v_i_3526_, v_entries_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3529_, lean_object* v_depth_3530_, lean_object* v_keys_3531_, lean_object* v_vals_3532_, lean_object* v_heq_3533_, lean_object* v_i_3534_, lean_object* v_entries_3535_){
_start:
{
size_t v_depth_boxed_3536_; lean_object* v_res_3537_; 
v_depth_boxed_3536_ = lean_unbox_usize(v_depth_3530_);
lean_dec(v_depth_3530_);
v_res_3537_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3529_, v_depth_boxed_3536_, v_keys_3531_, v_vals_3532_, v_heq_3533_, v_i_3534_, v_entries_3535_);
lean_dec_ref(v_vals_3532_);
lean_dec_ref(v_keys_3531_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3538_, lean_object* v_x_3539_, lean_object* v_x_3540_, lean_object* v_x_3541_, lean_object* v_x_3542_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3539_, v_x_3540_, v_x_3541_, v_x_3542_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3544_, lean_object* v_val_3545_, lean_object* v_name_3546_, lean_object* v_levelParams_3547_, uint8_t v___x_3548_, uint8_t v_hasTrace_3549_, lean_object* v_____r_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3556_; 
lean_inc_ref(v_val_3545_);
v___x_3556_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3544_, v_val_3545_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3558_; lean_object* v_a_3559_; lean_object* v___x_3560_; lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3577_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3557_);
lean_dec_ref(v___x_3556_);
v___x_3558_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3545_, v___y_3552_);
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref(v___x_3558_);
v___x_3560_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3557_, v___y_3552_);
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3563_ = v___x_3560_;
v_isShared_3564_ = v_isSharedCheck_3577_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3560_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3577_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
lean_inc_n(v_name_3546_, 2);
v___x_3565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3565_, 0, v_name_3546_);
lean_ctor_set(v___x_3565_, 1, v_levelParams_3547_);
lean_ctor_set(v___x_3565_, 2, v_a_3559_);
v___x_3566_ = lean_box(0);
v___x_3567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3567_, 0, v_name_3546_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3565_);
lean_ctor_set(v___x_3568_, 1, v_a_3561_);
lean_ctor_set(v___x_3568_, 2, v___x_3567_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set_tag(v___x_3563_, 2);
lean_ctor_set(v___x_3563_, 0, v___x_3568_);
v___x_3570_ = v___x_3563_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Lean_addDecl(v___x_3570_, v___x_3548_, v___y_3553_, v___y_3554_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v___x_3572_; uint8_t v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
lean_dec_ref(v___x_3571_);
v___x_3572_ = l_Lean_Meta_simpExtension;
v___x_3573_ = 0;
v___x_3574_ = lean_unsigned_to_nat(1000u);
v___x_3575_ = l_Lean_Meta_addSimpTheorem(v___x_3572_, v_name_3546_, v_hasTrace_3549_, v___x_3548_, v___x_3573_, v___x_3574_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
return v___x_3575_;
}
else
{
lean_dec(v_name_3546_);
return v___x_3571_;
}
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_levelParams_3547_);
lean_dec(v_name_3546_);
lean_dec_ref(v_val_3545_);
v_a_3578_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3556_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3556_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3586_, lean_object* v_val_3587_, lean_object* v_name_3588_, lean_object* v_levelParams_3589_, lean_object* v___x_3590_, lean_object* v_hasTrace_3591_, lean_object* v_____r_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
uint8_t v___x_9094__boxed_3598_; uint8_t v_hasTrace_boxed_3599_; lean_object* v_res_3600_; 
v___x_9094__boxed_3598_ = lean_unbox(v___x_3590_);
v_hasTrace_boxed_3599_ = lean_unbox(v_hasTrace_3591_);
v_res_3600_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3586_, v_val_3587_, v_name_3588_, v_levelParams_3589_, v___x_9094__boxed_3598_, v_hasTrace_boxed_3599_, v_____r_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3601_, lean_object* v_val_3602_, lean_object* v_name_3603_, lean_object* v_levelParams_3604_, uint8_t v___x_3605_, lean_object* v_____r_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v___x_3612_; 
lean_inc_ref(v_val_3602_);
v___x_3612_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3601_, v_val_3602_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3614_; lean_object* v_a_3615_; lean_object* v___x_3616_; lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3634_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref(v___x_3612_);
v___x_3614_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3602_, v___y_3608_);
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref(v___x_3614_);
v___x_3616_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3613_, v___y_3608_);
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3619_ = v___x_3616_;
v_isShared_3620_ = v_isSharedCheck_3634_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3616_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3634_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3626_; 
lean_inc_n(v_name_3603_, 2);
v___x_3621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3621_, 0, v_name_3603_);
lean_ctor_set(v___x_3621_, 1, v_levelParams_3604_);
lean_ctor_set(v___x_3621_, 2, v_a_3615_);
v___x_3622_ = lean_box(0);
v___x_3623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3623_, 0, v_name_3603_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
v___x_3624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3621_);
lean_ctor_set(v___x_3624_, 1, v_a_3617_);
lean_ctor_set(v___x_3624_, 2, v___x_3623_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set_tag(v___x_3619_, 2);
lean_ctor_set(v___x_3619_, 0, v___x_3624_);
v___x_3626_ = v___x_3619_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
uint8_t v___x_3627_; lean_object* v___x_3628_; 
v___x_3627_ = 0;
v___x_3628_ = l_Lean_addDecl(v___x_3626_, v___x_3627_, v___y_3609_, v___y_3610_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v___x_3629_; uint8_t v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
lean_dec_ref(v___x_3628_);
v___x_3629_ = l_Lean_Meta_simpExtension;
v___x_3630_ = 0;
v___x_3631_ = lean_unsigned_to_nat(1000u);
v___x_3632_ = l_Lean_Meta_addSimpTheorem(v___x_3629_, v_name_3603_, v___x_3605_, v___x_3627_, v___x_3630_, v___x_3631_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
return v___x_3632_;
}
else
{
lean_dec(v_name_3603_);
return v___x_3628_;
}
}
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_dec(v_levelParams_3604_);
lean_dec(v_name_3603_);
lean_dec_ref(v_val_3602_);
v_a_3635_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3612_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3612_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3643_, lean_object* v_val_3644_, lean_object* v_name_3645_, lean_object* v_levelParams_3646_, lean_object* v___x_3647_, lean_object* v_____r_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
uint8_t v___x_9182__boxed_3654_; lean_object* v_res_3655_; 
v___x_9182__boxed_3654_ = lean_unbox(v___x_3647_);
v_res_3655_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3643_, v_val_3644_, v_name_3645_, v_levelParams_3646_, v___x_9182__boxed_3654_, v_____r_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v_toConstantVal_3662_; lean_object* v_options_3663_; lean_object* v_name_3664_; lean_object* v_levelParams_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3885_; 
v_toConstantVal_3662_ = lean_ctor_get(v_ctorVal_3656_, 0);
lean_inc_ref(v_toConstantVal_3662_);
v_options_3663_ = lean_ctor_get(v_a_3659_, 2);
v_name_3664_ = lean_ctor_get(v_toConstantVal_3662_, 0);
v_levelParams_3665_ = lean_ctor_get(v_toConstantVal_3662_, 1);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_toConstantVal_3662_);
if (v_isSharedCheck_3885_ == 0)
{
lean_object* v_unused_3886_; 
v_unused_3886_ = lean_ctor_get(v_toConstantVal_3662_, 2);
lean_dec(v_unused_3886_);
v___x_3667_ = v_toConstantVal_3662_;
v_isShared_3668_ = v_isSharedCheck_3885_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_levelParams_3665_);
lean_inc(v_name_3664_);
lean_dec(v_toConstantVal_3662_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3885_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v_inheritedTraceOptions_3669_; uint8_t v_hasTrace_3670_; lean_object* v_name_3671_; 
v_inheritedTraceOptions_3669_ = lean_ctor_get(v_a_3659_, 13);
v_hasTrace_3670_ = lean_ctor_get_uint8(v_options_3663_, sizeof(void*)*1);
v_name_3671_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3664_);
if (v_hasTrace_3670_ == 0)
{
lean_object* v___x_3672_; 
lean_inc_ref(v_ctorVal_3656_);
v___x_3672_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3715_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3675_ = v___x_3672_;
v_isShared_3676_ = v_isSharedCheck_3715_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3672_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3715_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
if (lean_obj_tag(v_a_3673_) == 1)
{
lean_object* v_val_3677_; lean_object* v___x_3678_; 
lean_del_object(v___x_3675_);
v_val_3677_ = lean_ctor_get(v_a_3673_, 0);
lean_inc_n(v_val_3677_, 2);
lean_dec_ref(v_a_3673_);
v___x_3678_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3656_, v_val_3677_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3680_; lean_object* v_a_3681_; lean_object* v___x_3682_; lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3702_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref(v___x_3678_);
v___x_3680_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3677_, v_a_3658_);
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_a_3681_);
lean_dec_ref(v___x_3680_);
v___x_3682_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3679_, v_a_3658_);
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3702_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3702_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
lean_inc(v_name_3671_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 2, v_a_3681_);
lean_ctor_set(v___x_3667_, 0, v_name_3671_);
v___x_3688_ = v___x_3667_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_name_3671_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_levelParams_3665_);
lean_ctor_set(v_reuseFailAlloc_3701_, 2, v_a_3681_);
v___x_3688_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3689_ = lean_box(0);
lean_inc(v_name_3671_);
v___x_3690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3690_, 0, v_name_3671_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3688_);
lean_ctor_set(v___x_3691_, 1, v_a_3683_);
lean_ctor_set(v___x_3691_, 2, v___x_3690_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set_tag(v___x_3685_, 2);
lean_ctor_set(v___x_3685_, 0, v___x_3691_);
v___x_3693_ = v___x_3685_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_addDecl(v___x_3693_, v_hasTrace_3670_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v___x_3695_; uint8_t v___x_3696_; uint8_t v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec_ref(v___x_3694_);
v___x_3695_ = l_Lean_Meta_simpExtension;
v___x_3696_ = 1;
v___x_3697_ = 0;
v___x_3698_ = lean_unsigned_to_nat(1000u);
v___x_3699_ = l_Lean_Meta_addSimpTheorem(v___x_3695_, v_name_3671_, v___x_3696_, v_hasTrace_3670_, v___x_3697_, v___x_3698_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_3699_;
}
else
{
lean_dec(v_name_3671_);
return v___x_3694_;
}
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec(v_val_3677_);
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
v_a_3703_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3678_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3678_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3713_; 
lean_dec(v_a_3673_);
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v___x_3711_ = lean_box(0);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3711_);
v___x_3713_ = v___x_3675_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3711_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v_a_3716_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3672_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3672_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v___f_3724_; lean_object* v_cls_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v_a_3732_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v_a_3744_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v_a_3749_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v_a_3760_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v_a_3775_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v_a_3780_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; 
lean_inc(v_name_3671_);
v___f_3724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3724_, 0, v_name_3671_);
v_cls_3725_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_3726_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_3727_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_3728_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3669_, v_options_3663_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3823_; uint8_t v___x_3824_; 
v___x_3823_ = l_Lean_trace_profiler;
v___x_3824_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3663_, v___x_3823_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3825_; 
lean_dec_ref(v___f_3724_);
lean_inc_ref(v_ctorVal_3656_);
v___x_3825_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3876_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3828_ = v___x_3825_;
v_isShared_3829_ = v_isSharedCheck_3876_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3876_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
if (lean_obj_tag(v_a_3826_) == 1)
{
lean_object* v_val_3830_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; 
lean_del_object(v___x_3828_);
v_val_3830_ = lean_ctor_get(v_a_3826_, 0);
lean_inc(v_val_3830_);
lean_dec_ref(v_a_3826_);
if (v___x_3728_ == 0)
{
v___y_3832_ = v_a_3657_;
v___y_3833_ = v_a_3658_;
v___y_3834_ = v_a_3659_;
v___y_3835_ = v_a_3660_;
goto v___jp_3831_;
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3868_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
lean_inc(v_val_3830_);
v___x_3869_ = l_Lean_MessageData_ofExpr(v_val_3830_);
v___x_3870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3868_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
v___x_3871_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3725_, v___x_3870_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_dec_ref(v___x_3871_);
v___y_3832_ = v_a_3657_;
v___y_3833_ = v_a_3658_;
v___y_3834_ = v_a_3659_;
v___y_3835_ = v_a_3660_;
goto v___jp_3831_;
}
else
{
lean_dec(v_val_3830_);
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
return v___x_3871_;
}
}
v___jp_3831_:
{
lean_object* v___x_3836_; 
lean_inc(v_val_3830_);
v___x_3836_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3656_, v_val_3830_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3838_; lean_object* v_a_3839_; lean_object* v___x_3840_; lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3859_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref(v___x_3836_);
v___x_3838_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3830_, v___y_3833_);
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref(v___x_3838_);
v___x_3840_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3837_, v___y_3833_);
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3859_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3859_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
lean_inc(v_name_3671_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 2, v_a_3839_);
lean_ctor_set(v___x_3667_, 0, v_name_3671_);
v___x_3846_ = v___x_3667_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_name_3671_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v_levelParams_3665_);
lean_ctor_set(v_reuseFailAlloc_3858_, 2, v_a_3839_);
v___x_3846_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3851_; 
v___x_3847_ = lean_box(0);
lean_inc(v_name_3671_);
v___x_3848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3848_, 0, v_name_3671_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3846_);
lean_ctor_set(v___x_3849_, 1, v_a_3841_);
lean_ctor_set(v___x_3849_, 2, v___x_3848_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set_tag(v___x_3843_, 2);
lean_ctor_set(v___x_3843_, 0, v___x_3849_);
v___x_3851_ = v___x_3843_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3849_);
v___x_3851_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3852_; 
v___x_3852_ = l_Lean_addDecl(v___x_3851_, v___x_3824_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v___x_3853_; uint8_t v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
lean_dec_ref(v___x_3852_);
v___x_3853_ = l_Lean_Meta_simpExtension;
v___x_3854_ = 0;
v___x_3855_ = lean_unsigned_to_nat(1000u);
v___x_3856_ = l_Lean_Meta_addSimpTheorem(v___x_3853_, v_name_3671_, v_hasTrace_3670_, v___x_3824_, v___x_3854_, v___x_3855_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
return v___x_3856_;
}
else
{
lean_dec(v_name_3671_);
return v___x_3852_;
}
}
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_val_3830_);
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
v_a_3860_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3836_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3836_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
}
else
{
lean_object* v___x_3872_; lean_object* v___x_3874_; 
lean_dec(v_a_3826_);
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v___x_3872_ = lean_box(0);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 0, v___x_3872_);
v___x_3874_ = v___x_3828_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec(v_name_3671_);
lean_del_object(v___x_3667_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v_a_3877_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3825_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3825_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_del_object(v___x_3667_);
goto v___jp_3788_;
}
}
else
{
lean_del_object(v___x_3667_);
goto v___jp_3788_;
}
v___jp_3729_:
{
lean_object* v___x_3733_; double v___x_3734_; double v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3733_ = lean_io_get_num_heartbeats();
v___x_3734_ = lean_float_of_nat(v___y_3731_);
v___x_3735_ = lean_float_of_nat(v___x_3733_);
v___x_3736_ = lean_box_float(v___x_3734_);
v___x_3737_ = lean_box_float(v___x_3735_);
v___x_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3736_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3739_, 0, v_a_3732_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3725_, v_hasTrace_3670_, v___x_3726_, v_options_3663_, v___x_3728_, v___y_3730_, v___f_3724_, v___x_3739_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_3740_;
}
v___jp_3741_:
{
lean_object* v___x_3745_; 
v___x_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3745_, 0, v_a_3744_);
v___y_3730_ = v___y_3742_;
v___y_3731_ = v___y_3743_;
v_a_3732_ = v___x_3745_;
goto v___jp_3729_;
}
v___jp_3746_:
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3750_, 0, v_a_3749_);
v___y_3730_ = v___y_3747_;
v___y_3731_ = v___y_3748_;
v_a_3732_ = v___x_3750_;
goto v___jp_3729_;
}
v___jp_3751_:
{
if (lean_obj_tag(v___y_3754_) == 0)
{
lean_object* v_a_3755_; 
v_a_3755_ = lean_ctor_get(v___y_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref(v___y_3754_);
v___y_3747_ = v___y_3752_;
v___y_3748_ = v___y_3753_;
v_a_3749_ = v_a_3755_;
goto v___jp_3746_;
}
else
{
lean_object* v_a_3756_; 
v_a_3756_ = lean_ctor_get(v___y_3754_, 0);
lean_inc(v_a_3756_);
lean_dec_ref(v___y_3754_);
v___y_3742_ = v___y_3752_;
v___y_3743_ = v___y_3753_;
v_a_3744_ = v_a_3756_;
goto v___jp_3741_;
}
}
v___jp_3757_:
{
lean_object* v___x_3761_; double v___x_3762_; double v___x_3763_; double v___x_3764_; double v___x_3765_; double v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3761_ = lean_io_mono_nanos_now();
v___x_3762_ = lean_float_of_nat(v___y_3758_);
v___x_3763_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_3764_ = lean_float_div(v___x_3762_, v___x_3763_);
v___x_3765_ = lean_float_of_nat(v___x_3761_);
v___x_3766_ = lean_float_div(v___x_3765_, v___x_3763_);
v___x_3767_ = lean_box_float(v___x_3764_);
v___x_3768_ = lean_box_float(v___x_3766_);
v___x_3769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3770_, 0, v_a_3760_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3725_, v_hasTrace_3670_, v___x_3726_, v_options_3663_, v___x_3728_, v___y_3759_, v___f_3724_, v___x_3770_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_3771_;
}
v___jp_3772_:
{
lean_object* v___x_3776_; 
v___x_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3776_, 0, v_a_3775_);
v___y_3758_ = v___y_3773_;
v___y_3759_ = v___y_3774_;
v_a_3760_ = v___x_3776_;
goto v___jp_3757_;
}
v___jp_3777_:
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3781_, 0, v_a_3780_);
v___y_3758_ = v___y_3778_;
v___y_3759_ = v___y_3779_;
v_a_3760_ = v___x_3781_;
goto v___jp_3757_;
}
v___jp_3782_:
{
if (lean_obj_tag(v___y_3785_) == 0)
{
lean_object* v_a_3786_; 
v_a_3786_ = lean_ctor_get(v___y_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref(v___y_3785_);
v___y_3773_ = v___y_3783_;
v___y_3774_ = v___y_3784_;
v_a_3775_ = v_a_3786_;
goto v___jp_3772_;
}
else
{
lean_object* v_a_3787_; 
v_a_3787_ = lean_ctor_get(v___y_3785_, 0);
lean_inc(v_a_3787_);
lean_dec_ref(v___y_3785_);
v___y_3778_ = v___y_3783_;
v___y_3779_ = v___y_3784_;
v_a_3780_ = v_a_3787_;
goto v___jp_3777_;
}
}
v___jp_3788_:
{
lean_object* v___x_3789_; lean_object* v_a_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3789_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3660_);
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref(v___x_3789_);
v___x_3791_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3792_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3663_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3793_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3656_);
v___x_3794_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref(v___x_3794_);
if (lean_obj_tag(v_a_3795_) == 1)
{
if (v___x_3728_ == 0)
{
lean_object* v_val_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_val_3796_ = lean_ctor_get(v_a_3795_, 0);
lean_inc(v_val_3796_);
lean_dec_ref(v_a_3795_);
v___x_3797_ = lean_box(0);
v___x_3798_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3656_, v_val_3796_, v_name_3671_, v_levelParams_3665_, v___x_3792_, v_hasTrace_3670_, v___x_3797_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3783_ = v___x_3793_;
v___y_3784_ = v_a_3790_;
v___y_3785_ = v___x_3798_;
goto v___jp_3782_;
}
else
{
lean_object* v_val_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_val_3799_ = lean_ctor_get(v_a_3795_, 0);
lean_inc_n(v_val_3799_, 2);
lean_dec_ref(v_a_3795_);
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3801_ = l_Lean_MessageData_ofExpr(v_val_3799_);
v___x_3802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3800_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
v___x_3803_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3725_, v___x_3802_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3805_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref(v___x_3803_);
v___x_3805_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3656_, v_val_3799_, v_name_3671_, v_levelParams_3665_, v___x_3792_, v_hasTrace_3670_, v_a_3804_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3783_ = v___x_3793_;
v___y_3784_ = v_a_3790_;
v___y_3785_ = v___x_3805_;
goto v___jp_3782_;
}
else
{
lean_dec(v_val_3799_);
lean_dec(v_name_3671_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v___y_3783_ = v___x_3793_;
v___y_3784_ = v_a_3790_;
v___y_3785_ = v___x_3803_;
goto v___jp_3782_;
}
}
}
else
{
lean_object* v___x_3806_; 
lean_dec(v_a_3795_);
lean_dec(v_name_3671_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v___x_3806_ = lean_box(0);
v___y_3773_ = v___x_3793_;
v___y_3774_ = v_a_3790_;
v_a_3775_ = v___x_3806_;
goto v___jp_3772_;
}
}
else
{
lean_object* v_a_3807_; 
lean_dec(v_name_3671_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v_a_3807_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3807_);
lean_dec_ref(v___x_3794_);
v___y_3778_ = v___x_3793_;
v___y_3779_ = v_a_3790_;
v_a_3780_ = v_a_3807_;
goto v___jp_3777_;
}
}
else
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3656_);
v___x_3809_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref(v___x_3809_);
if (lean_obj_tag(v_a_3810_) == 1)
{
if (v___x_3728_ == 0)
{
lean_object* v_val_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v_val_3811_ = lean_ctor_get(v_a_3810_, 0);
lean_inc(v_val_3811_);
lean_dec_ref(v_a_3810_);
v___x_3812_ = lean_box(0);
v___x_3813_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3656_, v_val_3811_, v_name_3671_, v_levelParams_3665_, v___x_3792_, v___x_3812_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3752_ = v_a_3790_;
v___y_3753_ = v___x_3808_;
v___y_3754_ = v___x_3813_;
goto v___jp_3751_;
}
else
{
lean_object* v_val_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v_val_3814_ = lean_ctor_get(v_a_3810_, 0);
lean_inc_n(v_val_3814_, 2);
lean_dec_ref(v_a_3810_);
v___x_3815_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3816_ = l_Lean_MessageData_ofExpr(v_val_3814_);
v___x_3817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3815_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_3725_, v___x_3817_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v___x_3820_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref(v___x_3818_);
v___x_3820_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3656_, v_val_3814_, v_name_3671_, v_levelParams_3665_, v___x_3792_, v_a_3819_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
v___y_3752_ = v_a_3790_;
v___y_3753_ = v___x_3808_;
v___y_3754_ = v___x_3820_;
goto v___jp_3751_;
}
else
{
lean_dec(v_val_3814_);
lean_dec(v_name_3671_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v___y_3752_ = v_a_3790_;
v___y_3753_ = v___x_3808_;
v___y_3754_ = v___x_3818_;
goto v___jp_3751_;
}
}
}
else
{
lean_object* v___x_3821_; 
lean_dec(v_a_3810_);
lean_dec(v_name_3671_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v___x_3821_ = lean_box(0);
v___y_3747_ = v_a_3790_;
v___y_3748_ = v___x_3808_;
v_a_3749_ = v___x_3821_;
goto v___jp_3746_;
}
}
else
{
lean_object* v_a_3822_; 
lean_dec(v_name_3671_);
lean_dec(v_levelParams_3665_);
lean_dec_ref(v_ctorVal_3656_);
v_a_3822_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3822_);
lean_dec_ref(v___x_3809_);
v___y_3742_ = v_a_3790_;
v___y_3743_ = v___x_3808_;
v_a_3744_ = v_a_3822_;
goto v___jp_3741_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
lean_dec(v_a_3891_);
lean_dec_ref(v_a_3890_);
lean_dec(v_a_3889_);
lean_dec_ref(v_a_3888_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3894_, lean_object* v_decl_3895_, lean_object* v_ref_3896_){
_start:
{
lean_object* v_defValue_3898_; lean_object* v_descr_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3926_; 
v_defValue_3898_ = lean_ctor_get(v_decl_3895_, 0);
v_descr_3899_ = lean_ctor_get(v_decl_3895_, 1);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_decl_3895_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3901_ = v_decl_3895_;
v_isShared_3902_ = v_isSharedCheck_3926_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_descr_3899_);
lean_inc(v_defValue_3898_);
lean_dec(v_decl_3895_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3926_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; uint8_t v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3903_ = lean_alloc_ctor(1, 0, 1);
v___x_3904_ = lean_unbox(v_defValue_3898_);
lean_ctor_set_uint8(v___x_3903_, 0, v___x_3904_);
lean_inc_n(v_name_3894_, 2);
v___x_3905_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3905_, 0, v_name_3894_);
lean_ctor_set(v___x_3905_, 1, v_ref_3896_);
lean_ctor_set(v___x_3905_, 2, v___x_3903_);
lean_ctor_set(v___x_3905_, 3, v_descr_3899_);
v___x_3906_ = lean_register_option(v_name_3894_, v___x_3905_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3916_; 
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3916_ == 0)
{
lean_object* v_unused_3917_; 
v_unused_3917_ = lean_ctor_get(v___x_3906_, 0);
lean_dec(v_unused_3917_);
v___x_3908_ = v___x_3906_;
v_isShared_3909_ = v_isSharedCheck_3916_;
goto v_resetjp_3907_;
}
else
{
lean_dec(v___x_3906_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3916_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 1, v_defValue_3898_);
lean_ctor_set(v___x_3901_, 0, v_name_3894_);
v___x_3911_ = v___x_3901_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_name_3894_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_defValue_3898_);
v___x_3911_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3913_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3911_);
v___x_3913_ = v___x_3908_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
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
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_del_object(v___x_3901_);
lean_dec(v_defValue_3898_);
lean_dec(v_name_3894_);
v_a_3918_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3906_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3906_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_3927_, lean_object* v_decl_3928_, lean_object* v_ref_3929_, lean_object* v_a_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_3927_, v_decl_3928_, v_ref_3929_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3945_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_3946_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_3947_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_3948_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_3945_, v___x_3946_, v___x_3947_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_3951_, uint8_t v_isExporting_3952_, lean_object* v___x_3953_, lean_object* v___y_3954_, lean_object* v___x_3955_, lean_object* v_a_x3f_3956_){
_start:
{
lean_object* v___x_3958_; lean_object* v_env_3959_; lean_object* v_nextMacroScope_3960_; lean_object* v_ngen_3961_; lean_object* v_auxDeclNGen_3962_; lean_object* v_traceState_3963_; lean_object* v_messages_3964_; lean_object* v_infoState_3965_; lean_object* v_snapshotTasks_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3991_; 
v___x_3958_ = lean_st_ref_take(v___y_3951_);
v_env_3959_ = lean_ctor_get(v___x_3958_, 0);
v_nextMacroScope_3960_ = lean_ctor_get(v___x_3958_, 1);
v_ngen_3961_ = lean_ctor_get(v___x_3958_, 2);
v_auxDeclNGen_3962_ = lean_ctor_get(v___x_3958_, 3);
v_traceState_3963_ = lean_ctor_get(v___x_3958_, 4);
v_messages_3964_ = lean_ctor_get(v___x_3958_, 6);
v_infoState_3965_ = lean_ctor_get(v___x_3958_, 7);
v_snapshotTasks_3966_ = lean_ctor_get(v___x_3958_, 8);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3991_ == 0)
{
lean_object* v_unused_3992_; 
v_unused_3992_ = lean_ctor_get(v___x_3958_, 5);
lean_dec(v_unused_3992_);
v___x_3968_ = v___x_3958_;
v_isShared_3969_ = v_isSharedCheck_3991_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_snapshotTasks_3966_);
lean_inc(v_infoState_3965_);
lean_inc(v_messages_3964_);
lean_inc(v_traceState_3963_);
lean_inc(v_auxDeclNGen_3962_);
lean_inc(v_ngen_3961_);
lean_inc(v_nextMacroScope_3960_);
lean_inc(v_env_3959_);
lean_dec(v___x_3958_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3991_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3970_; lean_object* v___x_3972_; 
v___x_3970_ = l_Lean_Environment_setExporting(v_env_3959_, v_isExporting_3952_);
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 5, v___x_3953_);
lean_ctor_set(v___x_3968_, 0, v___x_3970_);
v___x_3972_ = v___x_3968_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3970_);
lean_ctor_set(v_reuseFailAlloc_3990_, 1, v_nextMacroScope_3960_);
lean_ctor_set(v_reuseFailAlloc_3990_, 2, v_ngen_3961_);
lean_ctor_set(v_reuseFailAlloc_3990_, 3, v_auxDeclNGen_3962_);
lean_ctor_set(v_reuseFailAlloc_3990_, 4, v_traceState_3963_);
lean_ctor_set(v_reuseFailAlloc_3990_, 5, v___x_3953_);
lean_ctor_set(v_reuseFailAlloc_3990_, 6, v_messages_3964_);
lean_ctor_set(v_reuseFailAlloc_3990_, 7, v_infoState_3965_);
lean_ctor_set(v_reuseFailAlloc_3990_, 8, v_snapshotTasks_3966_);
v___x_3972_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v_mctx_3975_; lean_object* v_zetaDeltaFVarIds_3976_; lean_object* v_postponed_3977_; lean_object* v_diag_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3988_; 
v___x_3973_ = lean_st_ref_set(v___y_3951_, v___x_3972_);
v___x_3974_ = lean_st_ref_take(v___y_3954_);
v_mctx_3975_ = lean_ctor_get(v___x_3974_, 0);
v_zetaDeltaFVarIds_3976_ = lean_ctor_get(v___x_3974_, 2);
v_postponed_3977_ = lean_ctor_get(v___x_3974_, 3);
v_diag_3978_ = lean_ctor_get(v___x_3974_, 4);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; 
v_unused_3989_ = lean_ctor_get(v___x_3974_, 1);
lean_dec(v_unused_3989_);
v___x_3980_ = v___x_3974_;
v_isShared_3981_ = v_isSharedCheck_3988_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_diag_3978_);
lean_inc(v_postponed_3977_);
lean_inc(v_zetaDeltaFVarIds_3976_);
lean_inc(v_mctx_3975_);
lean_dec(v___x_3974_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3988_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 1, v___x_3955_);
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_mctx_3975_);
lean_ctor_set(v_reuseFailAlloc_3987_, 1, v___x_3955_);
lean_ctor_set(v_reuseFailAlloc_3987_, 2, v_zetaDeltaFVarIds_3976_);
lean_ctor_set(v_reuseFailAlloc_3987_, 3, v_postponed_3977_);
lean_ctor_set(v_reuseFailAlloc_3987_, 4, v_diag_3978_);
v___x_3983_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3984_ = lean_st_ref_set(v___y_3954_, v___x_3983_);
v___x_3985_ = lean_box(0);
v___x_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
return v___x_3986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_3993_, lean_object* v_isExporting_3994_, lean_object* v___x_3995_, lean_object* v___y_3996_, lean_object* v___x_3997_, lean_object* v_a_x3f_3998_, lean_object* v___y_3999_){
_start:
{
uint8_t v_isExporting_boxed_4000_; lean_object* v_res_4001_; 
v_isExporting_boxed_4000_ = lean_unbox(v_isExporting_3994_);
v_res_4001_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_3993_, v_isExporting_boxed_4000_, v___x_3995_, v___y_3996_, v___x_3997_, v_a_x3f_3998_);
lean_dec(v_a_x3f_3998_);
lean_dec(v___y_3996_);
lean_dec(v___y_3993_);
return v_res_4001_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4002_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4003_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
return v___x_4004_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
lean_ctor_set(v___x_4006_, 1, v___x_4005_);
return v___x_4006_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4008_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
lean_ctor_set(v___x_4008_, 1, v___x_4007_);
lean_ctor_set(v___x_4008_, 2, v___x_4007_);
lean_ctor_set(v___x_4008_, 3, v___x_4007_);
lean_ctor_set(v___x_4008_, 4, v___x_4007_);
lean_ctor_set(v___x_4008_, 5, v___x_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4009_, uint8_t v_isExporting_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v___x_4016_; lean_object* v_env_4017_; uint8_t v_isExporting_4018_; lean_object* v___x_4019_; lean_object* v_env_4020_; lean_object* v_nextMacroScope_4021_; lean_object* v_ngen_4022_; lean_object* v_auxDeclNGen_4023_; lean_object* v_traceState_4024_; lean_object* v_messages_4025_; lean_object* v_infoState_4026_; lean_object* v_snapshotTasks_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4081_; 
v___x_4016_ = lean_st_ref_get(v___y_4014_);
v_env_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc_ref(v_env_4017_);
lean_dec(v___x_4016_);
v_isExporting_4018_ = lean_ctor_get_uint8(v_env_4017_, sizeof(void*)*8);
lean_dec_ref(v_env_4017_);
v___x_4019_ = lean_st_ref_take(v___y_4014_);
v_env_4020_ = lean_ctor_get(v___x_4019_, 0);
v_nextMacroScope_4021_ = lean_ctor_get(v___x_4019_, 1);
v_ngen_4022_ = lean_ctor_get(v___x_4019_, 2);
v_auxDeclNGen_4023_ = lean_ctor_get(v___x_4019_, 3);
v_traceState_4024_ = lean_ctor_get(v___x_4019_, 4);
v_messages_4025_ = lean_ctor_get(v___x_4019_, 6);
v_infoState_4026_ = lean_ctor_get(v___x_4019_, 7);
v_snapshotTasks_4027_ = lean_ctor_get(v___x_4019_, 8);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4081_ == 0)
{
lean_object* v_unused_4082_; 
v_unused_4082_ = lean_ctor_get(v___x_4019_, 5);
lean_dec(v_unused_4082_);
v___x_4029_ = v___x_4019_;
v_isShared_4030_ = v_isSharedCheck_4081_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_snapshotTasks_4027_);
lean_inc(v_infoState_4026_);
lean_inc(v_messages_4025_);
lean_inc(v_traceState_4024_);
lean_inc(v_auxDeclNGen_4023_);
lean_inc(v_ngen_4022_);
lean_inc(v_nextMacroScope_4021_);
lean_inc(v_env_4020_);
lean_dec(v___x_4019_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4081_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4034_; 
v___x_4031_ = l_Lean_Environment_setExporting(v_env_4020_, v_isExporting_4010_);
v___x_4032_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 5, v___x_4032_);
lean_ctor_set(v___x_4029_, 0, v___x_4031_);
v___x_4034_ = v___x_4029_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4031_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v_nextMacroScope_4021_);
lean_ctor_set(v_reuseFailAlloc_4080_, 2, v_ngen_4022_);
lean_ctor_set(v_reuseFailAlloc_4080_, 3, v_auxDeclNGen_4023_);
lean_ctor_set(v_reuseFailAlloc_4080_, 4, v_traceState_4024_);
lean_ctor_set(v_reuseFailAlloc_4080_, 5, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4080_, 6, v_messages_4025_);
lean_ctor_set(v_reuseFailAlloc_4080_, 7, v_infoState_4026_);
lean_ctor_set(v_reuseFailAlloc_4080_, 8, v_snapshotTasks_4027_);
v___x_4034_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v_mctx_4037_; lean_object* v_zetaDeltaFVarIds_4038_; lean_object* v_postponed_4039_; lean_object* v_diag_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4078_; 
v___x_4035_ = lean_st_ref_set(v___y_4014_, v___x_4034_);
v___x_4036_ = lean_st_ref_take(v___y_4012_);
v_mctx_4037_ = lean_ctor_get(v___x_4036_, 0);
v_zetaDeltaFVarIds_4038_ = lean_ctor_get(v___x_4036_, 2);
v_postponed_4039_ = lean_ctor_get(v___x_4036_, 3);
v_diag_4040_ = lean_ctor_get(v___x_4036_, 4);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4078_ == 0)
{
lean_object* v_unused_4079_; 
v_unused_4079_ = lean_ctor_get(v___x_4036_, 1);
lean_dec(v_unused_4079_);
v___x_4042_ = v___x_4036_;
v_isShared_4043_ = v_isSharedCheck_4078_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_diag_4040_);
lean_inc(v_postponed_4039_);
lean_inc(v_zetaDeltaFVarIds_4038_);
lean_inc(v_mctx_4037_);
lean_dec(v___x_4036_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4078_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4044_; lean_object* v___x_4046_; 
v___x_4044_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 1, v___x_4044_);
v___x_4046_ = v___x_4042_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_mctx_4037_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v___x_4044_);
lean_ctor_set(v_reuseFailAlloc_4077_, 2, v_zetaDeltaFVarIds_4038_);
lean_ctor_set(v_reuseFailAlloc_4077_, 3, v_postponed_4039_);
lean_ctor_set(v_reuseFailAlloc_4077_, 4, v_diag_4040_);
v___x_4046_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
lean_object* v___x_4047_; lean_object* v_r_4048_; 
v___x_4047_ = lean_st_ref_set(v___y_4012_, v___x_4046_);
lean_inc(v___y_4014_);
lean_inc_ref(v___y_4013_);
lean_inc(v___y_4012_);
lean_inc_ref(v___y_4011_);
v_r_4048_ = lean_apply_5(v_x_4009_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, lean_box(0));
if (lean_obj_tag(v_r_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4065_; 
v_a_4049_ = lean_ctor_get(v_r_4048_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_r_4048_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4051_ = v_r_4048_;
v_isShared_4052_ = v_isSharedCheck_4065_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v_r_4048_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4065_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
lean_inc(v_a_4049_);
if (v_isShared_4052_ == 0)
{
lean_ctor_set_tag(v___x_4051_, 1);
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
v___x_4055_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4014_, v_isExporting_4018_, v___x_4032_, v___y_4012_, v___x_4044_, v___x_4054_);
lean_dec_ref(v___x_4054_);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4062_ == 0)
{
lean_object* v_unused_4063_; 
v_unused_4063_ = lean_ctor_get(v___x_4055_, 0);
lean_dec(v_unused_4063_);
v___x_4057_ = v___x_4055_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_dec(v___x_4055_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
lean_ctor_set(v___x_4057_, 0, v_a_4049_);
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4049_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
else
{
lean_object* v_a_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
v_a_4066_ = lean_ctor_get(v_r_4048_, 0);
lean_inc(v_a_4066_);
lean_dec_ref(v_r_4048_);
v___x_4067_ = lean_box(0);
v___x_4068_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4014_, v_isExporting_4018_, v___x_4032_, v___y_4012_, v___x_4044_, v___x_4067_);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4075_ == 0)
{
lean_object* v_unused_4076_; 
v_unused_4076_ = lean_ctor_get(v___x_4068_, 0);
lean_dec(v_unused_4076_);
v___x_4070_ = v___x_4068_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_dec(v___x_4068_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
lean_ctor_set_tag(v___x_4070_, 1);
lean_ctor_set(v___x_4070_, 0, v_a_4066_);
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4066_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4083_, lean_object* v_isExporting_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
uint8_t v_isExporting_boxed_4090_; lean_object* v_res_4091_; 
v_isExporting_boxed_4090_ = lean_unbox(v_isExporting_4084_);
v_res_4091_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4083_, v_isExporting_boxed_4090_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4092_, lean_object* v_x_4093_, uint8_t v_isExporting_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4093_, v_isExporting_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4101_, lean_object* v_x_4102_, lean_object* v_isExporting_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
uint8_t v_isExporting_boxed_4109_; lean_object* v_res_4110_; 
v_isExporting_boxed_4109_ = lean_unbox(v_isExporting_4103_);
v_res_4110_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4101_, v_x_4102_, v_isExporting_boxed_4109_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4111_, lean_object* v_localInsts_4112_, lean_object* v_x_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4111_, v_localInsts_4112_, v_x_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4119_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4119_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
else
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4135_; 
v_a_4128_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4130_ = v___x_4119_;
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4119_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4128_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4136_, lean_object* v_localInsts_4137_, lean_object* v_x_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4136_, v_localInsts_4137_, v_x_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4145_, lean_object* v_lctx_4146_, lean_object* v_localInsts_4147_, lean_object* v_x_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v___x_4154_; 
v___x_4154_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4146_, v_localInsts_4147_, v_x_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4155_, lean_object* v_lctx_4156_, lean_object* v_localInsts_4157_, lean_object* v_x_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4155_, v_lctx_4156_, v_localInsts_4157_, v_x_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4165_, lean_object* v_x_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4172_ = l_Lean_MessageData_ofName(v_declName_4165_);
v___x_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4172_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4174_, lean_object* v_x_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4174_, v_x_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec_ref(v_x_4175_);
return v_res_4181_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4182_; 
v___x_4182_ = l_instMonadEIO(lean_box(0));
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v_toApplicative_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4256_; 
v___x_4193_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4194_ = l_StateRefT_x27_instMonad___redArg(v___x_4193_);
v_toApplicative_4195_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4256_ == 0)
{
lean_object* v_unused_4257_; 
v_unused_4257_ = lean_ctor_get(v___x_4194_, 1);
lean_dec(v_unused_4257_);
v___x_4197_ = v___x_4194_;
v_isShared_4198_ = v_isSharedCheck_4256_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_toApplicative_4195_);
lean_dec(v___x_4194_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4256_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v_toFunctor_4199_; lean_object* v_toSeq_4200_; lean_object* v_toSeqLeft_4201_; lean_object* v_toSeqRight_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4254_; 
v_toFunctor_4199_ = lean_ctor_get(v_toApplicative_4195_, 0);
v_toSeq_4200_ = lean_ctor_get(v_toApplicative_4195_, 2);
v_toSeqLeft_4201_ = lean_ctor_get(v_toApplicative_4195_, 3);
v_toSeqRight_4202_ = lean_ctor_get(v_toApplicative_4195_, 4);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_toApplicative_4195_);
if (v_isSharedCheck_4254_ == 0)
{
lean_object* v_unused_4255_; 
v_unused_4255_ = lean_ctor_get(v_toApplicative_4195_, 1);
lean_dec(v_unused_4255_);
v___x_4204_ = v_toApplicative_4195_;
v_isShared_4205_ = v_isSharedCheck_4254_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_toSeqRight_4202_);
lean_inc(v_toSeqLeft_4201_);
lean_inc(v_toSeq_4200_);
lean_inc(v_toFunctor_4199_);
lean_dec(v_toApplicative_4195_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4254_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___f_4206_; lean_object* v___f_4207_; lean_object* v___f_4208_; lean_object* v___f_4209_; lean_object* v___x_4210_; lean_object* v___f_4211_; lean_object* v___f_4212_; lean_object* v___f_4213_; lean_object* v___x_4215_; 
v___f_4206_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4207_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4199_);
v___f_4208_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4208_, 0, v_toFunctor_4199_);
v___f_4209_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4209_, 0, v_toFunctor_4199_);
v___x_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4210_, 0, v___f_4208_);
lean_ctor_set(v___x_4210_, 1, v___f_4209_);
v___f_4211_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4211_, 0, v_toSeqRight_4202_);
v___f_4212_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4212_, 0, v_toSeqLeft_4201_);
v___f_4213_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4213_, 0, v_toSeq_4200_);
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 4, v___f_4211_);
lean_ctor_set(v___x_4204_, 3, v___f_4212_);
lean_ctor_set(v___x_4204_, 2, v___f_4213_);
lean_ctor_set(v___x_4204_, 1, v___f_4206_);
lean_ctor_set(v___x_4204_, 0, v___x_4210_);
v___x_4215_ = v___x_4204_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4210_);
lean_ctor_set(v_reuseFailAlloc_4253_, 1, v___f_4206_);
lean_ctor_set(v_reuseFailAlloc_4253_, 2, v___f_4213_);
lean_ctor_set(v_reuseFailAlloc_4253_, 3, v___f_4212_);
lean_ctor_set(v_reuseFailAlloc_4253_, 4, v___f_4211_);
v___x_4215_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
lean_object* v___x_4217_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 1, v___f_4207_);
lean_ctor_set(v___x_4197_, 0, v___x_4215_);
v___x_4217_ = v___x_4197_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4215_);
lean_ctor_set(v_reuseFailAlloc_4252_, 1, v___f_4207_);
v___x_4217_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
lean_object* v___x_4218_; lean_object* v_toApplicative_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4250_; 
v___x_4218_ = l_StateRefT_x27_instMonad___redArg(v___x_4217_);
v_toApplicative_4219_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4250_ == 0)
{
lean_object* v_unused_4251_; 
v_unused_4251_ = lean_ctor_get(v___x_4218_, 1);
lean_dec(v_unused_4251_);
v___x_4221_ = v___x_4218_;
v_isShared_4222_ = v_isSharedCheck_4250_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_toApplicative_4219_);
lean_dec(v___x_4218_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4250_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v_toFunctor_4223_; lean_object* v_toSeq_4224_; lean_object* v_toSeqLeft_4225_; lean_object* v_toSeqRight_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4248_; 
v_toFunctor_4223_ = lean_ctor_get(v_toApplicative_4219_, 0);
v_toSeq_4224_ = lean_ctor_get(v_toApplicative_4219_, 2);
v_toSeqLeft_4225_ = lean_ctor_get(v_toApplicative_4219_, 3);
v_toSeqRight_4226_ = lean_ctor_get(v_toApplicative_4219_, 4);
v_isSharedCheck_4248_ = !lean_is_exclusive(v_toApplicative_4219_);
if (v_isSharedCheck_4248_ == 0)
{
lean_object* v_unused_4249_; 
v_unused_4249_ = lean_ctor_get(v_toApplicative_4219_, 1);
lean_dec(v_unused_4249_);
v___x_4228_ = v_toApplicative_4219_;
v_isShared_4229_ = v_isSharedCheck_4248_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_toSeqRight_4226_);
lean_inc(v_toSeqLeft_4225_);
lean_inc(v_toSeq_4224_);
lean_inc(v_toFunctor_4223_);
lean_dec(v_toApplicative_4219_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4248_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___f_4230_; lean_object* v___f_4231_; lean_object* v___f_4232_; lean_object* v___f_4233_; lean_object* v___x_4234_; lean_object* v___f_4235_; lean_object* v___f_4236_; lean_object* v___f_4237_; lean_object* v___x_4239_; 
v___f_4230_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4231_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4223_);
v___f_4232_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4232_, 0, v_toFunctor_4223_);
v___f_4233_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4233_, 0, v_toFunctor_4223_);
v___x_4234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4234_, 0, v___f_4232_);
lean_ctor_set(v___x_4234_, 1, v___f_4233_);
v___f_4235_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4235_, 0, v_toSeqRight_4226_);
v___f_4236_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4236_, 0, v_toSeqLeft_4225_);
v___f_4237_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4237_, 0, v_toSeq_4224_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 4, v___f_4235_);
lean_ctor_set(v___x_4228_, 3, v___f_4236_);
lean_ctor_set(v___x_4228_, 2, v___f_4237_);
lean_ctor_set(v___x_4228_, 1, v___f_4230_);
lean_ctor_set(v___x_4228_, 0, v___x_4234_);
v___x_4239_ = v___x_4228_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v___x_4234_);
lean_ctor_set(v_reuseFailAlloc_4247_, 1, v___f_4230_);
lean_ctor_set(v_reuseFailAlloc_4247_, 2, v___f_4237_);
lean_ctor_set(v_reuseFailAlloc_4247_, 3, v___f_4236_);
lean_ctor_set(v_reuseFailAlloc_4247_, 4, v___f_4235_);
v___x_4239_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4241_; 
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 1, v___f_4231_);
lean_ctor_set(v___x_4221_, 0, v___x_4239_);
v___x_4241_ = v___x_4221_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4239_);
lean_ctor_set(v_reuseFailAlloc_4246_, 1, v___f_4231_);
v___x_4241_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_19007__overap_4244_; lean_object* v___x_4245_; 
v___x_4242_ = lean_box(0);
v___x_4243_ = l_instInhabitedOfMonad___redArg(v___x_4241_, v___x_4242_);
v___x_19007__overap_4244_ = lean_panic_fn_borrowed(v___x_4243_, v_msg_4187_);
lean_dec(v___x_4243_);
lean_inc(v___y_4191_);
lean_inc_ref(v___y_4190_);
lean_inc(v___y_4189_);
lean_inc_ref(v___y_4188_);
v___x_4245_ = lean_apply_5(v___x_19007__overap_4244_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, lean_box(0));
return v___x_4245_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
return v_res_4264_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4266_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4267_ = l_Lean_stringToMessageData(v___x_4266_);
return v___x_4267_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4270_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4271_ = lean_unsigned_to_nat(11u);
v___x_4272_ = lean_unsigned_to_nat(122u);
v___x_4273_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4274_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4275_ = l_mkPanicMessageWithDecl(v___x_4274_, v___x_4273_, v___x_4272_, v___x_4271_, v___x_4270_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v___x_4290_; lean_object* v_env_4291_; uint8_t v___x_4292_; lean_object* v___x_4293_; 
v___x_4290_ = lean_st_ref_get(v___y_4280_);
v_env_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc_ref(v_env_4291_);
lean_dec(v___x_4290_);
v___x_4292_ = 0;
lean_inc(v_constName_4276_);
v___x_4293_ = l_Lean_Environment_findAsync_x3f(v_env_4291_, v_constName_4276_, v___x_4292_);
if (lean_obj_tag(v___x_4293_) == 1)
{
lean_object* v_val_4294_; uint8_t v_kind_4295_; 
v_val_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_val_4294_);
lean_dec_ref(v___x_4293_);
v_kind_4295_ = lean_ctor_get_uint8(v_val_4294_, sizeof(void*)*3);
if (v_kind_4295_ == 6)
{
lean_object* v___x_4296_; 
v___x_4296_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4294_);
if (lean_obj_tag(v___x_4296_) == 6)
{
lean_object* v_val_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
lean_dec(v_constName_4276_);
v_val_4297_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___x_4296_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_val_4297_);
lean_dec(v___x_4296_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
lean_ctor_set_tag(v___x_4299_, 0);
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_val_4297_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
return v___x_4302_;
}
}
}
else
{
lean_object* v___x_4305_; lean_object* v___x_4306_; 
lean_dec_ref(v___x_4296_);
v___x_4305_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4306_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4305_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4315_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4309_ = v___x_4306_;
v_isShared_4310_ = v_isSharedCheck_4315_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4306_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4315_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
if (lean_obj_tag(v_a_4307_) == 0)
{
lean_del_object(v___x_4309_);
goto v___jp_4282_;
}
else
{
lean_object* v_val_4311_; lean_object* v___x_4313_; 
lean_dec(v_constName_4276_);
v_val_4311_ = lean_ctor_get(v_a_4307_, 0);
lean_inc(v_val_4311_);
lean_dec_ref(v_a_4307_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 0, v_val_4311_);
v___x_4313_ = v___x_4309_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_val_4311_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
lean_dec(v_constName_4276_);
v_a_4316_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4306_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4306_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
}
else
{
lean_dec(v_val_4294_);
goto v___jp_4282_;
}
}
else
{
lean_dec(v___x_4293_);
goto v___jp_4282_;
}
v___jp_4282_:
{
lean_object* v___x_4283_; uint8_t v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4283_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4284_ = 0;
v___x_4285_ = l_Lean_MessageData_ofConstName(v_constName_4276_, v___x_4284_);
v___x_4286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4283_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4286_);
lean_ctor_set(v___x_4288_, 1, v___x_4287_);
v___x_4289_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4288_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
return v___x_4289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4331_, lean_object* v___x_4332_, lean_object* v___x_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v___x_4339_; 
v___x_4339_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4331_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4351_; 
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4342_ = v___x_4339_;
v_isShared_4343_ = v_isSharedCheck_4351_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4339_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4351_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v_numFields_4344_; uint8_t v___x_4345_; 
v_numFields_4344_ = lean_ctor_get(v_a_4340_, 4);
v___x_4345_ = lean_nat_dec_lt(v___x_4332_, v_numFields_4344_);
if (v___x_4345_ == 0)
{
lean_object* v___x_4347_; 
lean_dec(v_a_4340_);
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 0, v___x_4333_);
v___x_4347_ = v___x_4342_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v___x_4333_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
else
{
lean_object* v___x_4349_; 
lean_del_object(v___x_4342_);
lean_inc(v_a_4340_);
v___x_4349_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4340_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v___x_4350_; 
lean_dec_ref(v___x_4349_);
v___x_4350_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4340_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
return v___x_4350_;
}
else
{
lean_dec(v_a_4340_);
return v___x_4349_;
}
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
v_a_4352_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4339_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4339_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4360_, lean_object* v___x_4361_, lean_object* v___x_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4360_, v___x_4361_, v___x_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec(v___x_4361_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4369_, uint8_t v___x_4370_, lean_object* v_as_x27_4371_, lean_object* v_b_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
if (lean_obj_tag(v_as_x27_4371_) == 0)
{
lean_object* v___x_4378_; 
v___x_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4378_, 0, v_b_4372_);
return v___x_4378_;
}
else
{
lean_object* v_head_4379_; lean_object* v_tail_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___f_4383_; uint8_t v___y_4385_; uint8_t v___x_4388_; 
v_head_4379_ = lean_ctor_get(v_as_x27_4371_, 0);
lean_inc_n(v_head_4379_, 2);
v_tail_4380_ = lean_ctor_get(v_as_x27_4371_, 1);
lean_inc(v_tail_4380_);
lean_dec_ref(v_as_x27_4371_);
v___x_4381_ = lean_unsigned_to_nat(0u);
v___x_4382_ = lean_box(0);
v___f_4383_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4383_, 0, v_head_4379_);
lean_closure_set(v___f_4383_, 1, v___x_4381_);
lean_closure_set(v___f_4383_, 2, v___x_4382_);
v___x_4388_ = l_Lean_isPrivateName(v_head_4379_);
lean_dec(v_head_4379_);
if (v___x_4388_ == 0)
{
v___y_4385_ = v___y_4369_;
goto v___jp_4384_;
}
else
{
v___y_4385_ = v___x_4370_;
goto v___jp_4384_;
}
v___jp_4384_:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4383_, v___y_4385_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_dec_ref(v___x_4386_);
v_as_x27_4371_ = v_tail_4380_;
v_b_4372_ = v___x_4382_;
goto _start;
}
else
{
lean_dec(v_tail_4380_);
return v___x_4386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4389_, lean_object* v___x_4390_, lean_object* v_as_x27_4391_, lean_object* v_b_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
uint8_t v___y_20116__boxed_4398_; uint8_t v___x_20117__boxed_4399_; lean_object* v_res_4400_; 
v___y_20116__boxed_4398_ = lean_unbox(v___y_4389_);
v___x_20117__boxed_4399_ = lean_unbox(v___x_4390_);
v_res_4400_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_20116__boxed_4398_, v___x_20117__boxed_4399_, v_as_x27_4391_, v_b_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4401_, uint8_t v_hasTrace_4402_, lean_object* v_ctors_4403_, lean_object* v___x_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v___x_4410_; 
v___x_4410_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4401_, v_hasTrace_4402_, v_ctors_4403_, v___x_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4417_ == 0)
{
lean_object* v_unused_4418_; 
v_unused_4418_ = lean_ctor_get(v___x_4410_, 0);
lean_dec(v_unused_4418_);
v___x_4412_ = v___x_4410_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_dec(v___x_4410_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4404_);
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4404_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
else
{
return v___x_4410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4419_, lean_object* v_hasTrace_4420_, lean_object* v_ctors_4421_, lean_object* v___x_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
uint8_t v___y_20161__boxed_4428_; uint8_t v_hasTrace_boxed_4429_; lean_object* v_res_4430_; 
v___y_20161__boxed_4428_ = lean_unbox(v___y_4419_);
v_hasTrace_boxed_4429_ = lean_unbox(v_hasTrace_4420_);
v_res_4430_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_20161__boxed_4428_, v_hasTrace_boxed_4429_, v_ctors_4421_, v___x_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
return v_res_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2(uint8_t v_hasTrace_4431_, uint8_t v___x_4432_, lean_object* v_ctors_4433_, lean_object* v___x_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v___x_4440_; 
v___x_4440_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v_hasTrace_4431_, v___x_4432_, v_ctors_4433_, v___x_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4447_ == 0)
{
lean_object* v_unused_4448_; 
v_unused_4448_ = lean_ctor_get(v___x_4440_, 0);
lean_dec(v_unused_4448_);
v___x_4442_ = v___x_4440_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_dec(v___x_4440_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 0, v___x_4434_);
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4434_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
else
{
return v___x_4440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed(lean_object* v_hasTrace_4449_, lean_object* v___x_4450_, lean_object* v_ctors_4451_, lean_object* v___x_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
uint8_t v_hasTrace_boxed_4458_; uint8_t v___x_20202__boxed_4459_; lean_object* v_res_4460_; 
v_hasTrace_boxed_4458_ = lean_unbox(v_hasTrace_4449_);
v___x_20202__boxed_4459_ = lean_unbox(v___x_4450_);
v_res_4460_ = l_Lean_Meta_mkInjectiveTheorems___lam__2(v_hasTrace_boxed_4458_, v___x_20202__boxed_4459_, v_ctors_4451_, v___x_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3(uint8_t v___x_4461_, uint8_t v_isUnsafe_4462_, lean_object* v_ctors_4463_, lean_object* v___x_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v___x_4470_; 
v___x_4470_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4461_, v_isUnsafe_4462_, v_ctors_4463_, v___x_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4477_ == 0)
{
lean_object* v_unused_4478_; 
v_unused_4478_ = lean_ctor_get(v___x_4470_, 0);
lean_dec(v_unused_4478_);
v___x_4472_ = v___x_4470_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_dec(v___x_4470_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 0, v___x_4464_);
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4464_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
else
{
return v___x_4470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed(lean_object* v___x_4479_, lean_object* v_isUnsafe_4480_, lean_object* v_ctors_4481_, lean_object* v___x_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_){
_start:
{
uint8_t v___x_20243__boxed_4488_; uint8_t v_isUnsafe_boxed_4489_; lean_object* v_res_4490_; 
v___x_20243__boxed_4488_ = lean_unbox(v___x_4479_);
v_isUnsafe_boxed_4489_ = lean_unbox(v_isUnsafe_4480_);
v_res_4490_ = l_Lean_Meta_mkInjectiveTheorems___lam__3(v___x_20243__boxed_4488_, v_isUnsafe_boxed_4489_, v_ctors_4481_, v___x_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
return v_res_4490_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4492_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4493_ = l_Lean_stringToMessageData(v___x_4492_);
return v___x_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_){
_start:
{
lean_object* v___x_4500_; lean_object* v_env_4501_; lean_object* v___x_4502_; 
v___x_4500_ = lean_st_ref_get(v___y_4498_);
v_env_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc_ref(v_env_4501_);
lean_dec(v___x_4500_);
lean_inc(v_constName_4494_);
v___x_4502_ = l_Lean_isInductiveCore_x3f(v_env_4501_, v_constName_4494_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v___x_4503_; uint8_t v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4503_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4504_ = 0;
v___x_4505_ = l_Lean_MessageData_ofConstName(v_constName_4494_, v___x_4504_);
v___x_4506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4503_);
lean_ctor_set(v___x_4506_, 1, v___x_4505_);
v___x_4507_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4506_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
v___x_4509_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4508_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
return v___x_4509_;
}
else
{
lean_object* v_val_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
lean_dec(v_constName_4494_);
v_val_4510_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4502_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_val_4510_);
lean_dec(v___x_4502_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
lean_ctor_set_tag(v___x_4512_, 0);
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_val_4510_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
return v_res_4524_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4525_; 
v___x_4525_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4525_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4526_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4526_);
return v___x_4527_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4528_ = lean_unsigned_to_nat(32u);
v___x_4529_ = lean_mk_empty_array_with_capacity(v___x_4528_);
v___x_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
return v___x_4530_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4531_ = ((size_t)5ULL);
v___x_4532_ = lean_unsigned_to_nat(0u);
v___x_4533_ = lean_unsigned_to_nat(32u);
v___x_4534_ = lean_mk_empty_array_with_capacity(v___x_4533_);
v___x_4535_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4536_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
lean_ctor_set(v___x_4536_, 1, v___x_4534_);
lean_ctor_set(v___x_4536_, 2, v___x_4532_);
lean_ctor_set(v___x_4536_, 3, v___x_4532_);
lean_ctor_set_usize(v___x_4536_, 4, v___x_4531_);
return v___x_4536_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4537_ = lean_box(1);
v___x_4538_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4539_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4539_);
lean_ctor_set(v___x_4540_, 1, v___x_4538_);
lean_ctor_set(v___x_4540_, 2, v___x_4537_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4549_ = lean_st_ref_get(v_a_4547_);
lean_inc(v_declName_4543_);
v___x_4550_ = l_Lean_Meta_isInductivePredicate(v_declName_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4747_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4553_ = v___x_4550_;
v_isShared_4554_ = v_isSharedCheck_4747_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4550_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4747_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v_env_4560_; lean_object* v___f_4561_; lean_object* v___x_4562_; uint8_t v___x_4563_; lean_object* v___y_4565_; lean_object* v___y_4566_; uint8_t v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v_a_4571_; lean_object* v___y_4581_; lean_object* v___y_4582_; uint8_t v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v_a_4587_; lean_object* v___y_4590_; lean_object* v___y_4591_; uint8_t v___y_4592_; lean_object* v___y_4593_; lean_object* v___y_4594_; lean_object* v___y_4595_; lean_object* v_a_4596_; lean_object* v___y_4599_; lean_object* v___y_4600_; uint8_t v___y_4601_; lean_object* v___y_4602_; lean_object* v___y_4603_; lean_object* v___y_4604_; lean_object* v_a_4605_; lean_object* v___y_4618_; lean_object* v___y_4619_; uint8_t v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v___y_4623_; lean_object* v_a_4624_; lean_object* v___y_4627_; lean_object* v___y_4628_; uint8_t v___y_4629_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v_a_4633_; uint8_t v___y_4636_; lean_object* v___y_4637_; lean_object* v___y_4638_; uint8_t v___y_4639_; lean_object* v___y_4640_; uint8_t v___y_4678_; uint8_t v___x_4743_; 
v_env_4560_ = lean_ctor_get(v___x_4549_, 0);
lean_inc_ref(v_env_4560_);
lean_dec(v___x_4549_);
lean_inc(v_declName_4543_);
v___f_4561_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4561_, 0, v_declName_4543_);
v___x_4562_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4563_ = 1;
v___x_4743_ = l_Lean_Environment_contains(v_env_4560_, v___x_4562_, v___x_4563_);
if (v___x_4743_ == 0)
{
v___y_4678_ = v___x_4743_;
goto v___jp_4677_;
}
else
{
lean_object* v_options_4744_; lean_object* v___x_4745_; uint8_t v___x_4746_; 
v_options_4744_ = lean_ctor_get(v_a_4546_, 2);
v___x_4745_ = l_Lean_Meta_genInjectivity;
v___x_4746_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4744_, v___x_4745_);
v___y_4678_ = v___x_4746_;
goto v___jp_4677_;
}
v___jp_4555_:
{
lean_object* v___x_4556_; lean_object* v___x_4558_; 
v___x_4556_ = lean_box(0);
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 0, v___x_4556_);
v___x_4558_ = v___x_4553_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4556_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
v___jp_4564_:
{
lean_object* v___x_4572_; double v___x_4573_; double v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4572_ = lean_io_get_num_heartbeats();
v___x_4573_ = lean_float_of_nat(v___y_4570_);
v___x_4574_ = lean_float_of_nat(v___x_4572_);
v___x_4575_ = lean_box_float(v___x_4573_);
v___x_4576_ = lean_box_float(v___x_4574_);
v___x_4577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4575_);
lean_ctor_set(v___x_4577_, 1, v___x_4576_);
v___x_4578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4578_, 0, v_a_4571_);
lean_ctor_set(v___x_4578_, 1, v___x_4577_);
lean_inc_ref(v___y_4565_);
lean_inc(v___y_4566_);
v___x_4579_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4566_, v___x_4563_, v___y_4565_, v___y_4569_, v___y_4567_, v___y_4568_, v___f_4561_, v___x_4578_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
return v___x_4579_;
}
v___jp_4580_:
{
lean_object* v___x_4588_; 
v___x_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4588_, 0, v_a_4587_);
v___y_4565_ = v___y_4582_;
v___y_4566_ = v___y_4581_;
v___y_4567_ = v___y_4583_;
v___y_4568_ = v___y_4584_;
v___y_4569_ = v___y_4585_;
v___y_4570_ = v___y_4586_;
v_a_4571_ = v___x_4588_;
goto v___jp_4564_;
}
v___jp_4589_:
{
lean_object* v___x_4597_; 
v___x_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4597_, 0, v_a_4596_);
v___y_4565_ = v___y_4591_;
v___y_4566_ = v___y_4590_;
v___y_4567_ = v___y_4592_;
v___y_4568_ = v___y_4593_;
v___y_4569_ = v___y_4594_;
v___y_4570_ = v___y_4595_;
v_a_4571_ = v___x_4597_;
goto v___jp_4564_;
}
v___jp_4598_:
{
lean_object* v___x_4606_; double v___x_4607_; double v___x_4608_; double v___x_4609_; double v___x_4610_; double v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4606_ = lean_io_mono_nanos_now();
v___x_4607_ = lean_float_of_nat(v___y_4602_);
v___x_4608_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0);
v___x_4609_ = lean_float_div(v___x_4607_, v___x_4608_);
v___x_4610_ = lean_float_of_nat(v___x_4606_);
v___x_4611_ = lean_float_div(v___x_4610_, v___x_4608_);
v___x_4612_ = lean_box_float(v___x_4609_);
v___x_4613_ = lean_box_float(v___x_4611_);
v___x_4614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4612_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
v___x_4615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4615_, 0, v_a_4605_);
lean_ctor_set(v___x_4615_, 1, v___x_4614_);
lean_inc_ref(v___y_4599_);
lean_inc(v___y_4600_);
v___x_4616_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4600_, v___x_4563_, v___y_4599_, v___y_4604_, v___y_4601_, v___y_4603_, v___f_4561_, v___x_4615_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
return v___x_4616_;
}
v___jp_4617_:
{
lean_object* v___x_4625_; 
v___x_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4625_, 0, v_a_4624_);
v___y_4599_ = v___y_4619_;
v___y_4600_ = v___y_4618_;
v___y_4601_ = v___y_4620_;
v___y_4602_ = v___y_4621_;
v___y_4603_ = v___y_4622_;
v___y_4604_ = v___y_4623_;
v_a_4605_ = v___x_4625_;
goto v___jp_4598_;
}
v___jp_4626_:
{
lean_object* v___x_4634_; 
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v_a_4633_);
v___y_4599_ = v___y_4628_;
v___y_4600_ = v___y_4627_;
v___y_4601_ = v___y_4629_;
v___y_4602_ = v___y_4630_;
v___y_4603_ = v___y_4631_;
v___y_4604_ = v___y_4632_;
v_a_4605_ = v___x_4634_;
goto v___jp_4598_;
}
v___jp_4635_:
{
lean_object* v___x_4641_; lean_object* v_a_4642_; lean_object* v___x_4643_; uint8_t v___x_4644_; 
v___x_4641_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4547_);
v_a_4642_ = lean_ctor_get(v___x_4641_, 0);
lean_inc(v_a_4642_);
lean_dec_ref(v___x_4641_);
v___x_4643_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4644_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4640_, v___x_4643_);
if (v___x_4644_ == 0)
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = lean_io_mono_nanos_now();
v___x_4646_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; uint8_t v_isUnsafe_4648_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4647_);
lean_dec_ref(v___x_4646_);
v_isUnsafe_4648_ = lean_ctor_get_uint8(v_a_4647_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4648_ == 0)
{
lean_object* v_ctors_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___f_4655_; lean_object* v___x_4656_; 
v_ctors_4649_ = lean_ctor_get(v_a_4647_, 4);
lean_inc(v_ctors_4649_);
lean_dec(v_a_4647_);
v___x_4650_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4651_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4652_ = lean_box(0);
v___x_4653_ = lean_box(v___y_4636_);
v___x_4654_ = lean_box(v___x_4644_);
v___f_4655_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4655_, 0, v___x_4653_);
lean_closure_set(v___f_4655_, 1, v___x_4654_);
lean_closure_set(v___f_4655_, 2, v_ctors_4649_);
lean_closure_set(v___f_4655_, 3, v___x_4652_);
v___x_4656_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4650_, v___x_4651_, v___f_4655_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_a_4657_);
lean_dec_ref(v___x_4656_);
v___y_4618_ = v___y_4637_;
v___y_4619_ = v___y_4638_;
v___y_4620_ = v___y_4639_;
v___y_4621_ = v___x_4645_;
v___y_4622_ = v_a_4642_;
v___y_4623_ = v___y_4640_;
v_a_4624_ = v_a_4657_;
goto v___jp_4617_;
}
else
{
lean_object* v_a_4658_; 
v_a_4658_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_a_4658_);
lean_dec_ref(v___x_4656_);
v___y_4627_ = v___y_4637_;
v___y_4628_ = v___y_4638_;
v___y_4629_ = v___y_4639_;
v___y_4630_ = v___x_4645_;
v___y_4631_ = v_a_4642_;
v___y_4632_ = v___y_4640_;
v_a_4633_ = v_a_4658_;
goto v___jp_4626_;
}
}
else
{
lean_object* v___x_4659_; 
lean_dec(v_a_4647_);
v___x_4659_ = lean_box(0);
v___y_4618_ = v___y_4637_;
v___y_4619_ = v___y_4638_;
v___y_4620_ = v___y_4639_;
v___y_4621_ = v___x_4645_;
v___y_4622_ = v_a_4642_;
v___y_4623_ = v___y_4640_;
v_a_4624_ = v___x_4659_;
goto v___jp_4617_;
}
}
else
{
lean_object* v_a_4660_; 
v_a_4660_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4660_);
lean_dec_ref(v___x_4646_);
v___y_4627_ = v___y_4637_;
v___y_4628_ = v___y_4638_;
v___y_4629_ = v___y_4639_;
v___y_4630_ = v___x_4645_;
v___y_4631_ = v_a_4642_;
v___y_4632_ = v___y_4640_;
v_a_4633_ = v_a_4660_;
goto v___jp_4626_;
}
}
else
{
lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4661_ = lean_io_get_num_heartbeats();
v___x_4662_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; uint8_t v_isUnsafe_4664_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4663_);
lean_dec_ref(v___x_4662_);
v_isUnsafe_4664_ = lean_ctor_get_uint8(v_a_4663_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4664_ == 0)
{
lean_object* v_ctors_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___f_4671_; lean_object* v___x_4672_; 
v_ctors_4665_ = lean_ctor_get(v_a_4663_, 4);
lean_inc(v_ctors_4665_);
lean_dec(v_a_4663_);
v___x_4666_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4667_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4668_ = lean_box(0);
v___x_4669_ = lean_box(v___x_4644_);
v___x_4670_ = lean_box(v_isUnsafe_4664_);
v___f_4671_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed), 9, 4);
lean_closure_set(v___f_4671_, 0, v___x_4669_);
lean_closure_set(v___f_4671_, 1, v___x_4670_);
lean_closure_set(v___f_4671_, 2, v_ctors_4665_);
lean_closure_set(v___f_4671_, 3, v___x_4668_);
v___x_4672_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4666_, v___x_4667_, v___f_4671_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_a_4673_);
lean_dec_ref(v___x_4672_);
v___y_4581_ = v___y_4637_;
v___y_4582_ = v___y_4638_;
v___y_4583_ = v___y_4639_;
v___y_4584_ = v_a_4642_;
v___y_4585_ = v___y_4640_;
v___y_4586_ = v___x_4661_;
v_a_4587_ = v_a_4673_;
goto v___jp_4580_;
}
else
{
lean_object* v_a_4674_; 
v_a_4674_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_a_4674_);
lean_dec_ref(v___x_4672_);
v___y_4590_ = v___y_4637_;
v___y_4591_ = v___y_4638_;
v___y_4592_ = v___y_4639_;
v___y_4593_ = v_a_4642_;
v___y_4594_ = v___y_4640_;
v___y_4595_ = v___x_4661_;
v_a_4596_ = v_a_4674_;
goto v___jp_4589_;
}
}
else
{
lean_object* v___x_4675_; 
lean_dec(v_a_4663_);
v___x_4675_ = lean_box(0);
v___y_4581_ = v___y_4637_;
v___y_4582_ = v___y_4638_;
v___y_4583_ = v___y_4639_;
v___y_4584_ = v_a_4642_;
v___y_4585_ = v___y_4640_;
v___y_4586_ = v___x_4661_;
v_a_4587_ = v___x_4675_;
goto v___jp_4580_;
}
}
else
{
lean_object* v_a_4676_; 
v_a_4676_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4676_);
lean_dec_ref(v___x_4662_);
v___y_4590_ = v___y_4637_;
v___y_4591_ = v___y_4638_;
v___y_4592_ = v___y_4639_;
v___y_4593_ = v_a_4642_;
v___y_4594_ = v___y_4640_;
v___y_4595_ = v___x_4661_;
v_a_4596_ = v_a_4676_;
goto v___jp_4589_;
}
}
}
v___jp_4677_:
{
if (v___y_4678_ == 0)
{
lean_dec_ref(v___f_4561_);
lean_dec(v_a_4551_);
lean_dec(v_declName_4543_);
goto v___jp_4555_;
}
else
{
uint8_t v___x_4679_; 
v___x_4679_ = lean_unbox(v_a_4551_);
lean_dec(v_a_4551_);
if (v___x_4679_ == 0)
{
lean_object* v_options_4680_; uint8_t v_hasTrace_4681_; 
lean_del_object(v___x_4553_);
v_options_4680_ = lean_ctor_get(v_a_4546_, 2);
v_hasTrace_4681_ = lean_ctor_get_uint8(v_options_4680_, sizeof(void*)*1);
if (v_hasTrace_4681_ == 0)
{
lean_object* v___x_4682_; 
lean_dec_ref(v___f_4561_);
v___x_4682_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4700_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4685_ = v___x_4682_;
v_isShared_4686_ = v_isSharedCheck_4700_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4682_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4700_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
uint8_t v_isUnsafe_4687_; 
v_isUnsafe_4687_ = lean_ctor_get_uint8(v_a_4683_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4687_ == 0)
{
lean_object* v_ctors_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___f_4694_; lean_object* v___x_4695_; 
lean_del_object(v___x_4685_);
v_ctors_4688_ = lean_ctor_get(v_a_4683_, 4);
lean_inc(v_ctors_4688_);
lean_dec(v_a_4683_);
v___x_4689_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4690_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4691_ = lean_box(0);
v___x_4692_ = lean_box(v___y_4678_);
v___x_4693_ = lean_box(v_hasTrace_4681_);
v___f_4694_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4694_, 0, v___x_4692_);
lean_closure_set(v___f_4694_, 1, v___x_4693_);
lean_closure_set(v___f_4694_, 2, v_ctors_4688_);
lean_closure_set(v___f_4694_, 3, v___x_4691_);
v___x_4695_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4689_, v___x_4690_, v___f_4694_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
return v___x_4695_;
}
else
{
lean_object* v___x_4696_; lean_object* v___x_4698_; 
lean_dec(v_a_4683_);
v___x_4696_ = lean_box(0);
if (v_isShared_4686_ == 0)
{
lean_ctor_set(v___x_4685_, 0, v___x_4696_);
v___x_4698_ = v___x_4685_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v___x_4696_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
}
else
{
lean_object* v_a_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4708_; 
v_a_4701_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4703_ = v___x_4682_;
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_a_4701_);
lean_dec(v___x_4682_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4708_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4706_; 
if (v_isShared_4704_ == 0)
{
v___x_4706_ = v___x_4703_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4701_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
v_inheritedTraceOptions_4709_ = lean_ctor_get(v_a_4546_, 13);
v___x_4710_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4711_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___closed__1));
v___x_4712_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9);
v___x_4713_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4709_, v_options_4680_, v___x_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; uint8_t v___x_4715_; 
v___x_4714_ = l_Lean_trace_profiler;
v___x_4715_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4680_, v___x_4714_);
if (v___x_4715_ == 0)
{
lean_object* v___x_4716_; 
lean_dec_ref(v___f_4561_);
v___x_4716_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4734_; 
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4719_ = v___x_4716_;
v_isShared_4720_ = v_isSharedCheck_4734_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_a_4717_);
lean_dec(v___x_4716_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4734_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
uint8_t v_isUnsafe_4721_; 
v_isUnsafe_4721_ = lean_ctor_get_uint8(v_a_4717_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4721_ == 0)
{
lean_object* v_ctors_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___f_4728_; lean_object* v___x_4729_; 
lean_del_object(v___x_4719_);
v_ctors_4722_ = lean_ctor_get(v_a_4717_, 4);
lean_inc(v_ctors_4722_);
lean_dec(v_a_4717_);
v___x_4723_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4724_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4725_ = lean_box(0);
v___x_4726_ = lean_box(v_hasTrace_4681_);
v___x_4727_ = lean_box(v___x_4715_);
v___f_4728_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4728_, 0, v___x_4726_);
lean_closure_set(v___f_4728_, 1, v___x_4727_);
lean_closure_set(v___f_4728_, 2, v_ctors_4722_);
lean_closure_set(v___f_4728_, 3, v___x_4725_);
v___x_4729_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4723_, v___x_4724_, v___f_4728_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
return v___x_4729_;
}
else
{
lean_object* v___x_4730_; lean_object* v___x_4732_; 
lean_dec(v_a_4717_);
v___x_4730_ = lean_box(0);
if (v_isShared_4720_ == 0)
{
lean_ctor_set(v___x_4719_, 0, v___x_4730_);
v___x_4732_ = v___x_4719_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4730_);
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
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
v_a_4735_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4737_ = v___x_4716_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4716_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
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
v___y_4636_ = v_hasTrace_4681_;
v___y_4637_ = v___x_4710_;
v___y_4638_ = v___x_4711_;
v___y_4639_ = v___x_4713_;
v___y_4640_ = v_options_4680_;
goto v___jp_4635_;
}
}
else
{
v___y_4636_ = v_hasTrace_4681_;
v___y_4637_ = v___x_4710_;
v___y_4638_ = v___x_4711_;
v___y_4639_ = v___x_4713_;
v___y_4640_ = v_options_4680_;
goto v___jp_4635_;
}
}
}
else
{
lean_dec_ref(v___f_4561_);
lean_dec(v_declName_4543_);
goto v___jp_4555_;
}
}
}
}
}
else
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4755_; 
lean_dec(v___x_4549_);
lean_dec(v_declName_4543_);
v_a_4748_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4750_ = v___x_4550_;
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v___x_4550_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v___x_4753_; 
if (v_isShared_4751_ == 0)
{
v___x_4753_ = v___x_4750_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_a_4748_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
lean_dec(v_a_4760_);
lean_dec_ref(v_a_4759_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4763_, uint8_t v___x_4764_, lean_object* v_as_4765_, lean_object* v_as_x27_4766_, lean_object* v_b_4767_, lean_object* v_a_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_){
_start:
{
lean_object* v___x_4774_; 
v___x_4774_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4763_, v___x_4764_, v_as_x27_4766_, v_b_4767_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4775_, lean_object* v___x_4776_, lean_object* v_as_4777_, lean_object* v_as_x27_4778_, lean_object* v_b_4779_, lean_object* v_a_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_){
_start:
{
uint8_t v___y_20870__boxed_4786_; uint8_t v___x_20871__boxed_4787_; lean_object* v_res_4788_; 
v___y_20870__boxed_4786_ = lean_unbox(v___y_4775_);
v___x_20871__boxed_4787_ = lean_unbox(v___x_4776_);
v_res_4788_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_20870__boxed_4786_, v___x_20871__boxed_4787_, v_as_4777_, v_as_x27_4778_, v_b_4779_, v_a_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec(v_as_4777_);
return v_res_4788_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4829_ = lean_unsigned_to_nat(4172903888u);
v___x_4830_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4831_ = l_Lean_Name_num___override(v___x_4830_, v___x_4829_);
return v___x_4831_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4833_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4834_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4835_ = l_Lean_Name_str___override(v___x_4834_, v___x_4833_);
return v___x_4835_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4837_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4838_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4839_ = l_Lean_Name_str___override(v___x_4838_, v___x_4837_);
return v___x_4839_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4840_ = lean_unsigned_to_nat(2u);
v___x_4841_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4842_ = l_Lean_Name_num___override(v___x_4841_, v___x_4840_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4844_; uint8_t v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4844_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4845_ = 0;
v___x_4846_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4847_ = l_Lean_registerTraceClass(v___x_4844_, v___x_4845_, v___x_4846_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4850_, lean_object* v_b_4851_){
_start:
{
lean_object* v_array_4852_; lean_object* v_start_4853_; lean_object* v_stop_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4867_; 
v_array_4852_ = lean_ctor_get(v_a_4850_, 0);
v_start_4853_ = lean_ctor_get(v_a_4850_, 1);
v_stop_4854_ = lean_ctor_get(v_a_4850_, 2);
v_isSharedCheck_4867_ = !lean_is_exclusive(v_a_4850_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4856_ = v_a_4850_;
v_isShared_4857_ = v_isSharedCheck_4867_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_stop_4854_);
lean_inc(v_start_4853_);
lean_inc(v_array_4852_);
lean_dec(v_a_4850_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4867_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
uint8_t v___x_4858_; 
v___x_4858_ = lean_nat_dec_lt(v_start_4853_, v_stop_4854_);
if (v___x_4858_ == 0)
{
lean_del_object(v___x_4856_);
lean_dec(v_stop_4854_);
lean_dec(v_start_4853_);
lean_dec_ref(v_array_4852_);
return v_b_4851_;
}
else
{
lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4862_; 
v___x_4859_ = lean_unsigned_to_nat(1u);
v___x_4860_ = lean_nat_add(v_start_4853_, v___x_4859_);
lean_inc_ref(v_array_4852_);
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 1, v___x_4860_);
v___x_4862_ = v___x_4856_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_array_4852_);
lean_ctor_set(v_reuseFailAlloc_4866_, 1, v___x_4860_);
lean_ctor_set(v_reuseFailAlloc_4866_, 2, v_stop_4854_);
v___x_4862_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4863_ = lean_array_fget(v_array_4852_, v_start_4853_);
lean_dec(v_start_4853_);
lean_dec_ref(v_array_4852_);
v___x_4864_ = lean_array_push(v_b_4851_, v___x_4863_);
v_a_4850_ = v___x_4862_;
v_b_4851_ = v___x_4864_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4868_; 
v___x_4868_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4868_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4869_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4869_);
return v___x_4870_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4872_ = lean_unsigned_to_nat(0u);
v___x_4873_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4872_);
lean_ctor_set(v___x_4873_, 1, v___x_4872_);
lean_ctor_set(v___x_4873_, 2, v___x_4872_);
lean_ctor_set(v___x_4873_, 3, v___x_4872_);
lean_ctor_set(v___x_4873_, 4, v___x_4871_);
lean_ctor_set(v___x_4873_, 5, v___x_4871_);
lean_ctor_set(v___x_4873_, 6, v___x_4871_);
lean_ctor_set(v___x_4873_, 7, v___x_4871_);
lean_ctor_set(v___x_4873_, 8, v___x_4871_);
lean_ctor_set(v___x_4873_, 9, v___x_4871_);
return v___x_4873_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4874_ = lean_box(1);
v___x_4875_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4876_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4877_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4876_);
lean_ctor_set(v___x_4877_, 1, v___x_4875_);
lean_ctor_set(v___x_4877_, 2, v___x_4874_);
return v___x_4877_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_4880_ = l_Lean_stringToMessageData(v___x_4879_);
return v___x_4880_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4882_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_4883_ = l_Lean_stringToMessageData(v___x_4882_);
return v___x_4883_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4885_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_4886_ = l_Lean_stringToMessageData(v___x_4885_);
return v___x_4886_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4888_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_4889_ = l_Lean_stringToMessageData(v___x_4888_);
return v___x_4889_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; 
v___x_4891_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_4892_ = l_Lean_stringToMessageData(v___x_4891_);
return v___x_4892_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4894_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_4895_ = l_Lean_stringToMessageData(v___x_4894_);
return v___x_4895_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4897_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_4898_ = l_Lean_stringToMessageData(v___x_4897_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4899_, lean_object* v_declHint_4900_, lean_object* v___y_4901_){
_start:
{
lean_object* v___x_4903_; lean_object* v_env_4904_; uint8_t v___x_4905_; 
v___x_4903_ = lean_st_ref_get(v___y_4901_);
v_env_4904_ = lean_ctor_get(v___x_4903_, 0);
lean_inc_ref(v_env_4904_);
lean_dec(v___x_4903_);
v___x_4905_ = l_Lean_Name_isAnonymous(v_declHint_4900_);
if (v___x_4905_ == 0)
{
uint8_t v_isExporting_4906_; 
v_isExporting_4906_ = lean_ctor_get_uint8(v_env_4904_, sizeof(void*)*8);
if (v_isExporting_4906_ == 0)
{
lean_object* v___x_4907_; 
lean_dec_ref(v_env_4904_);
lean_dec(v_declHint_4900_);
v___x_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4907_, 0, v_msg_4899_);
return v___x_4907_;
}
else
{
lean_object* v___x_4908_; uint8_t v___x_4909_; 
lean_inc_ref(v_env_4904_);
v___x_4908_ = l_Lean_Environment_setExporting(v_env_4904_, v___x_4905_);
lean_inc(v_declHint_4900_);
lean_inc_ref(v___x_4908_);
v___x_4909_ = l_Lean_Environment_contains(v___x_4908_, v_declHint_4900_, v_isExporting_4906_);
if (v___x_4909_ == 0)
{
lean_object* v___x_4910_; 
lean_dec_ref(v___x_4908_);
lean_dec_ref(v_env_4904_);
lean_dec(v_declHint_4900_);
v___x_4910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4910_, 0, v_msg_4899_);
return v___x_4910_;
}
else
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v_c_4916_; lean_object* v___x_4917_; 
v___x_4911_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4912_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_4913_ = l_Lean_Options_empty;
v___x_4914_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4908_);
lean_ctor_set(v___x_4914_, 1, v___x_4911_);
lean_ctor_set(v___x_4914_, 2, v___x_4912_);
lean_ctor_set(v___x_4914_, 3, v___x_4913_);
lean_inc(v_declHint_4900_);
v___x_4915_ = l_Lean_MessageData_ofConstName(v_declHint_4900_, v___x_4905_);
v_c_4916_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4916_, 0, v___x_4914_);
lean_ctor_set(v_c_4916_, 1, v___x_4915_);
v___x_4917_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4904_, v_declHint_4900_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; 
lean_dec_ref(v_env_4904_);
lean_dec(v_declHint_4900_);
v___x_4918_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4918_);
lean_ctor_set(v___x_4919_, 1, v_c_4916_);
v___x_4920_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_4921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4919_);
lean_ctor_set(v___x_4921_, 1, v___x_4920_);
v___x_4922_ = l_Lean_MessageData_note(v___x_4921_);
v___x_4923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4923_, 0, v_msg_4899_);
lean_ctor_set(v___x_4923_, 1, v___x_4922_);
v___x_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4924_, 0, v___x_4923_);
return v___x_4924_;
}
else
{
lean_object* v_val_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4960_; 
v_val_4925_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4927_ = v___x_4917_;
v_isShared_4928_ = v_isSharedCheck_4960_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_val_4925_);
lean_dec(v___x_4917_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4960_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v_mod_4932_; uint8_t v___x_4933_; 
v___x_4929_ = lean_box(0);
v___x_4930_ = l_Lean_Environment_header(v_env_4904_);
lean_dec_ref(v_env_4904_);
v___x_4931_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4930_);
v_mod_4932_ = lean_array_get(v___x_4929_, v___x_4931_, v_val_4925_);
lean_dec(v_val_4925_);
lean_dec_ref(v___x_4931_);
v___x_4933_ = l_Lean_isPrivateName(v_declHint_4900_);
lean_dec(v_declHint_4900_);
if (v___x_4933_ == 0)
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4945_; 
v___x_4934_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_4935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4934_);
lean_ctor_set(v___x_4935_, 1, v_c_4916_);
v___x_4936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_4937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4935_);
lean_ctor_set(v___x_4937_, 1, v___x_4936_);
v___x_4938_ = l_Lean_MessageData_ofName(v_mod_4932_);
v___x_4939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4937_);
lean_ctor_set(v___x_4939_, 1, v___x_4938_);
v___x_4940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_4941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4939_);
lean_ctor_set(v___x_4941_, 1, v___x_4940_);
v___x_4942_ = l_Lean_MessageData_note(v___x_4941_);
v___x_4943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4943_, 0, v_msg_4899_);
lean_ctor_set(v___x_4943_, 1, v___x_4942_);
if (v_isShared_4928_ == 0)
{
lean_ctor_set_tag(v___x_4927_, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4943_);
v___x_4945_ = v___x_4927_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v___x_4943_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
else
{
lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4958_; 
v___x_4947_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4947_);
lean_ctor_set(v___x_4948_, 1, v_c_4916_);
v___x_4949_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_4950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4948_);
lean_ctor_set(v___x_4950_, 1, v___x_4949_);
v___x_4951_ = l_Lean_MessageData_ofName(v_mod_4932_);
v___x_4952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4950_);
lean_ctor_set(v___x_4952_, 1, v___x_4951_);
v___x_4953_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_4954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4952_);
lean_ctor_set(v___x_4954_, 1, v___x_4953_);
v___x_4955_ = l_Lean_MessageData_note(v___x_4954_);
v___x_4956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4956_, 0, v_msg_4899_);
lean_ctor_set(v___x_4956_, 1, v___x_4955_);
if (v_isShared_4928_ == 0)
{
lean_ctor_set_tag(v___x_4927_, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4956_);
v___x_4958_ = v___x_4927_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v___x_4956_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4961_; 
lean_dec_ref(v_env_4904_);
lean_dec(v_declHint_4900_);
v___x_4961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4961_, 0, v_msg_4899_);
return v___x_4961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_4962_, lean_object* v_declHint_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4962_, v_declHint_4963_, v___y_4964_);
lean_dec(v___y_4964_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_4967_, lean_object* v_declHint_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_){
_start:
{
lean_object* v___x_4974_; lean_object* v_a_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4984_; 
v___x_4974_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_4967_, v_declHint_4968_, v___y_4972_);
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4977_ = v___x_4974_;
v_isShared_4978_ = v_isSharedCheck_4984_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v___x_4974_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4984_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4982_; 
v___x_4979_ = l_Lean_unknownIdentifierMessageTag;
v___x_4980_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4979_);
lean_ctor_set(v___x_4980_, 1, v_a_4975_);
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 0, v___x_4980_);
v___x_4982_ = v___x_4977_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v___x_4980_);
v___x_4982_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
return v___x_4982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_4985_, lean_object* v_declHint_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
lean_object* v_res_4992_; 
v_res_4992_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_4985_, v_declHint_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
lean_dec(v___y_4988_);
lean_dec_ref(v___y_4987_);
return v_res_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_4993_, lean_object* v_msg_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_){
_start:
{
lean_object* v_fileName_5000_; lean_object* v_fileMap_5001_; lean_object* v_options_5002_; lean_object* v_currRecDepth_5003_; lean_object* v_maxRecDepth_5004_; lean_object* v_ref_5005_; lean_object* v_currNamespace_5006_; lean_object* v_openDecls_5007_; lean_object* v_initHeartbeats_5008_; lean_object* v_maxHeartbeats_5009_; lean_object* v_quotContext_5010_; lean_object* v_currMacroScope_5011_; uint8_t v_diag_5012_; lean_object* v_cancelTk_x3f_5013_; uint8_t v_suppressElabErrors_5014_; lean_object* v_inheritedTraceOptions_5015_; lean_object* v_ref_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
v_fileName_5000_ = lean_ctor_get(v___y_4997_, 0);
v_fileMap_5001_ = lean_ctor_get(v___y_4997_, 1);
v_options_5002_ = lean_ctor_get(v___y_4997_, 2);
v_currRecDepth_5003_ = lean_ctor_get(v___y_4997_, 3);
v_maxRecDepth_5004_ = lean_ctor_get(v___y_4997_, 4);
v_ref_5005_ = lean_ctor_get(v___y_4997_, 5);
v_currNamespace_5006_ = lean_ctor_get(v___y_4997_, 6);
v_openDecls_5007_ = lean_ctor_get(v___y_4997_, 7);
v_initHeartbeats_5008_ = lean_ctor_get(v___y_4997_, 8);
v_maxHeartbeats_5009_ = lean_ctor_get(v___y_4997_, 9);
v_quotContext_5010_ = lean_ctor_get(v___y_4997_, 10);
v_currMacroScope_5011_ = lean_ctor_get(v___y_4997_, 11);
v_diag_5012_ = lean_ctor_get_uint8(v___y_4997_, sizeof(void*)*14);
v_cancelTk_x3f_5013_ = lean_ctor_get(v___y_4997_, 12);
v_suppressElabErrors_5014_ = lean_ctor_get_uint8(v___y_4997_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5015_ = lean_ctor_get(v___y_4997_, 13);
v_ref_5016_ = l_Lean_replaceRef(v_ref_4993_, v_ref_5005_);
lean_inc_ref(v_inheritedTraceOptions_5015_);
lean_inc(v_cancelTk_x3f_5013_);
lean_inc(v_currMacroScope_5011_);
lean_inc(v_quotContext_5010_);
lean_inc(v_maxHeartbeats_5009_);
lean_inc(v_initHeartbeats_5008_);
lean_inc(v_openDecls_5007_);
lean_inc(v_currNamespace_5006_);
lean_inc(v_maxRecDepth_5004_);
lean_inc(v_currRecDepth_5003_);
lean_inc_ref(v_options_5002_);
lean_inc_ref(v_fileMap_5001_);
lean_inc_ref(v_fileName_5000_);
v___x_5017_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5017_, 0, v_fileName_5000_);
lean_ctor_set(v___x_5017_, 1, v_fileMap_5001_);
lean_ctor_set(v___x_5017_, 2, v_options_5002_);
lean_ctor_set(v___x_5017_, 3, v_currRecDepth_5003_);
lean_ctor_set(v___x_5017_, 4, v_maxRecDepth_5004_);
lean_ctor_set(v___x_5017_, 5, v_ref_5016_);
lean_ctor_set(v___x_5017_, 6, v_currNamespace_5006_);
lean_ctor_set(v___x_5017_, 7, v_openDecls_5007_);
lean_ctor_set(v___x_5017_, 8, v_initHeartbeats_5008_);
lean_ctor_set(v___x_5017_, 9, v_maxHeartbeats_5009_);
lean_ctor_set(v___x_5017_, 10, v_quotContext_5010_);
lean_ctor_set(v___x_5017_, 11, v_currMacroScope_5011_);
lean_ctor_set(v___x_5017_, 12, v_cancelTk_x3f_5013_);
lean_ctor_set(v___x_5017_, 13, v_inheritedTraceOptions_5015_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*14, v_diag_5012_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*14 + 1, v_suppressElabErrors_5014_);
v___x_5018_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_4994_, v___y_4995_, v___y_4996_, v___x_5017_, v___y_4998_);
lean_dec_ref(v___x_5017_);
return v___x_5018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5019_, lean_object* v_msg_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_){
_start:
{
lean_object* v_res_5026_; 
v_res_5026_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5019_, v_msg_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
lean_dec(v_ref_5019_);
return v_res_5026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5027_, lean_object* v_msg_5028_, lean_object* v_declHint_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
lean_object* v___x_5035_; lean_object* v_a_5036_; lean_object* v___x_5037_; 
v___x_5035_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5028_, v_declHint_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_);
v_a_5036_ = lean_ctor_get(v___x_5035_, 0);
lean_inc(v_a_5036_);
lean_dec_ref(v___x_5035_);
v___x_5037_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5027_, v_a_5036_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_);
return v___x_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5038_, lean_object* v_msg_5039_, lean_object* v_declHint_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5038_, v_msg_5039_, v_declHint_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
lean_dec(v_ref_5038_);
return v_res_5046_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5048_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5049_ = l_Lean_stringToMessageData(v___x_5048_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5050_, lean_object* v_constName_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_){
_start:
{
lean_object* v___x_5057_; uint8_t v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
v___x_5057_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5058_ = 0;
lean_inc(v_constName_5051_);
v___x_5059_ = l_Lean_MessageData_ofConstName(v_constName_5051_, v___x_5058_);
v___x_5060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5060_, 0, v___x_5057_);
lean_ctor_set(v___x_5060_, 1, v___x_5059_);
v___x_5061_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5060_);
lean_ctor_set(v___x_5062_, 1, v___x_5061_);
v___x_5063_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5050_, v___x_5062_, v_constName_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
return v___x_5063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5064_, lean_object* v_constName_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_){
_start:
{
lean_object* v_res_5071_; 
v_res_5071_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5064_, v_constName_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_);
lean_dec(v___y_5069_);
lean_dec_ref(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec_ref(v___y_5066_);
lean_dec(v_ref_5064_);
return v_res_5071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_){
_start:
{
lean_object* v_ref_5078_; lean_object* v___x_5079_; 
v_ref_5078_ = lean_ctor_get(v___y_5075_, 5);
v___x_5079_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5078_, v_constName_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
return v___x_5079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
lean_dec(v___y_5084_);
lean_dec_ref(v___y_5083_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_){
_start:
{
lean_object* v___x_5093_; lean_object* v_env_5094_; uint8_t v___x_5095_; lean_object* v___x_5096_; 
v___x_5093_ = lean_st_ref_get(v___y_5091_);
v_env_5094_ = lean_ctor_get(v___x_5093_, 0);
lean_inc_ref(v_env_5094_);
lean_dec(v___x_5093_);
v___x_5095_ = 0;
lean_inc(v_constName_5087_);
v___x_5096_ = l_Lean_Environment_find_x3f(v_env_5094_, v_constName_5087_, v___x_5095_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v___x_5097_; 
v___x_5097_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_);
return v___x_5097_;
}
else
{
lean_object* v_val_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5105_; 
lean_dec(v_constName_5087_);
v_val_5098_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5100_ = v___x_5096_;
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_val_5098_);
lean_dec(v___x_5096_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
lean_object* v___x_5103_; 
if (v_isShared_5101_ == 0)
{
lean_ctor_set_tag(v___x_5100_, 0);
v___x_5103_ = v___x_5100_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_val_5098_);
v___x_5103_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
return v___x_5103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_);
lean_dec(v___y_5110_);
lean_dec_ref(v___y_5109_);
lean_dec(v___y_5108_);
lean_dec_ref(v___y_5107_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5115_, lean_object* v_x_5116_, lean_object* v_x_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
if (lean_obj_tag(v_x_5115_) == 5)
{
lean_object* v_fn_5123_; lean_object* v_arg_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
v_fn_5123_ = lean_ctor_get(v_x_5115_, 0);
lean_inc_ref(v_fn_5123_);
v_arg_5124_ = lean_ctor_get(v_x_5115_, 1);
lean_inc_ref(v_arg_5124_);
lean_dec_ref(v_x_5115_);
v___x_5125_ = lean_array_set(v_x_5116_, v_x_5117_, v_arg_5124_);
v___x_5126_ = lean_unsigned_to_nat(1u);
v___x_5127_ = lean_nat_sub(v_x_5117_, v___x_5126_);
lean_dec(v_x_5117_);
v_x_5115_ = v_fn_5123_;
v_x_5116_ = v___x_5125_;
v_x_5117_ = v___x_5127_;
goto _start;
}
else
{
lean_dec(v_x_5117_);
if (lean_obj_tag(v_x_5115_) == 4)
{
lean_object* v_declName_5129_; lean_object* v___x_5130_; 
v_declName_5129_ = lean_ctor_get(v_x_5115_, 0);
lean_inc(v_declName_5129_);
lean_dec_ref(v_x_5115_);
v___x_5130_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5129_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5162_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5133_ = v___x_5130_;
v_isShared_5134_ = v_isSharedCheck_5162_;
goto v_resetjp_5132_;
}
else
{
lean_inc(v_a_5131_);
lean_dec(v___x_5130_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5162_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
lean_object* v_lower_5136_; lean_object* v_upper_5137_; 
if (lean_obj_tag(v_a_5131_) == 5)
{
lean_object* v_val_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5159_; 
v_val_5145_ = lean_ctor_get(v_a_5131_, 0);
v_isSharedCheck_5159_ = !lean_is_exclusive(v_a_5131_);
if (v_isSharedCheck_5159_ == 0)
{
v___x_5147_ = v_a_5131_;
v_isShared_5148_ = v_isSharedCheck_5159_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_val_5145_);
lean_dec(v_a_5131_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5159_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v_numParams_5149_; lean_object* v_numIndices_5150_; lean_object* v___x_5151_; uint8_t v___x_5152_; 
v_numParams_5149_ = lean_ctor_get(v_val_5145_, 1);
lean_inc(v_numParams_5149_);
v_numIndices_5150_ = lean_ctor_get(v_val_5145_, 2);
lean_inc(v_numIndices_5150_);
lean_dec_ref(v_val_5145_);
v___x_5151_ = lean_unsigned_to_nat(0u);
v___x_5152_ = lean_nat_dec_eq(v_numIndices_5150_, v___x_5151_);
lean_dec(v_numIndices_5150_);
if (v___x_5152_ == 0)
{
lean_object* v___x_5153_; uint8_t v___x_5154_; 
lean_del_object(v___x_5147_);
v___x_5153_ = lean_array_get_size(v_x_5116_);
v___x_5154_ = lean_nat_dec_le(v_numParams_5149_, v___x_5151_);
if (v___x_5154_ == 0)
{
v_lower_5136_ = v_numParams_5149_;
v_upper_5137_ = v___x_5153_;
goto v___jp_5135_;
}
else
{
lean_dec(v_numParams_5149_);
v_lower_5136_ = v___x_5151_;
v_upper_5137_ = v___x_5153_;
goto v___jp_5135_;
}
}
else
{
lean_object* v___x_5155_; lean_object* v___x_5157_; 
lean_dec(v_numParams_5149_);
lean_del_object(v___x_5133_);
lean_dec_ref(v_x_5116_);
v___x_5155_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5148_ == 0)
{
lean_ctor_set_tag(v___x_5147_, 0);
lean_ctor_set(v___x_5147_, 0, v___x_5155_);
v___x_5157_ = v___x_5147_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v___x_5155_);
v___x_5157_ = v_reuseFailAlloc_5158_;
goto v_reusejp_5156_;
}
v_reusejp_5156_:
{
return v___x_5157_;
}
}
}
}
else
{
lean_object* v___x_5160_; lean_object* v___x_5161_; 
lean_del_object(v___x_5133_);
lean_dec(v_a_5131_);
lean_dec_ref(v_x_5116_);
v___x_5160_ = lean_box(0);
v___x_5161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5161_, 0, v___x_5160_);
return v___x_5161_;
}
v___jp_5135_:
{
lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5143_; 
v___x_5138_ = l_Array_toSubarray___redArg(v_x_5116_, v_lower_5136_, v_upper_5137_);
v___x_5139_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5140_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5138_, v___x_5139_);
v___x_5141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5140_);
if (v_isShared_5134_ == 0)
{
lean_ctor_set(v___x_5133_, 0, v___x_5141_);
v___x_5143_ = v___x_5133_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v___x_5141_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
}
else
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5170_; 
lean_dec_ref(v_x_5116_);
v_a_5163_ = lean_ctor_get(v___x_5130_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5165_ = v___x_5130_;
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5130_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v___x_5168_; 
if (v_isShared_5166_ == 0)
{
v___x_5168_ = v___x_5165_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_a_5163_);
v___x_5168_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
return v___x_5168_;
}
}
}
}
else
{
lean_object* v___x_5171_; lean_object* v___x_5172_; 
lean_dec_ref(v_x_5116_);
lean_dec_ref(v_x_5115_);
v___x_5171_ = lean_box(0);
v___x_5172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5172_, 0, v___x_5171_);
return v___x_5172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5173_, lean_object* v_x_5174_, lean_object* v_x_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5173_, v_x_5174_, v_x_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
lean_dec(v___y_5177_);
lean_dec_ref(v___y_5176_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_){
_start:
{
lean_object* v___x_5188_; 
lean_inc(v_a_5186_);
lean_inc_ref(v_a_5185_);
lean_inc(v_a_5184_);
lean_inc_ref(v_a_5183_);
v___x_5188_ = lean_infer_type(v_ctorApp_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_);
if (lean_obj_tag(v___x_5188_) == 0)
{
lean_object* v_a_5189_; lean_object* v___x_5190_; 
v_a_5189_ = lean_ctor_get(v___x_5188_, 0);
lean_inc(v_a_5189_);
lean_dec_ref(v___x_5188_);
v___x_5190_ = l_Lean_Meta_whnfD(v_a_5189_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_);
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_object* v_a_5191_; lean_object* v_dummy_5192_; lean_object* v_nargs_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; 
v_a_5191_ = lean_ctor_get(v___x_5190_, 0);
lean_inc(v_a_5191_);
lean_dec_ref(v___x_5190_);
v_dummy_5192_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5193_ = l_Lean_Expr_getAppNumArgs(v_a_5191_);
lean_inc(v_nargs_5193_);
v___x_5194_ = lean_mk_array(v_nargs_5193_, v_dummy_5192_);
v___x_5195_ = lean_unsigned_to_nat(1u);
v___x_5196_ = lean_nat_sub(v_nargs_5193_, v___x_5195_);
lean_dec(v_nargs_5193_);
v___x_5197_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5191_, v___x_5194_, v___x_5196_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_);
return v___x_5197_;
}
else
{
lean_object* v_a_5198_; lean_object* v___x_5200_; uint8_t v_isShared_5201_; uint8_t v_isSharedCheck_5205_; 
v_a_5198_ = lean_ctor_get(v___x_5190_, 0);
v_isSharedCheck_5205_ = !lean_is_exclusive(v___x_5190_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5200_ = v___x_5190_;
v_isShared_5201_ = v_isSharedCheck_5205_;
goto v_resetjp_5199_;
}
else
{
lean_inc(v_a_5198_);
lean_dec(v___x_5190_);
v___x_5200_ = lean_box(0);
v_isShared_5201_ = v_isSharedCheck_5205_;
goto v_resetjp_5199_;
}
v_resetjp_5199_:
{
lean_object* v___x_5203_; 
if (v_isShared_5201_ == 0)
{
v___x_5203_ = v___x_5200_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
v___x_5203_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
return v___x_5203_;
}
}
}
}
else
{
lean_object* v_a_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5213_; 
v_a_5206_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5213_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5213_ == 0)
{
v___x_5208_ = v___x_5188_;
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_a_5206_);
lean_dec(v___x_5188_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
lean_object* v___x_5211_; 
if (v_isShared_5209_ == 0)
{
v___x_5211_ = v___x_5208_;
goto v_reusejp_5210_;
}
else
{
lean_object* v_reuseFailAlloc_5212_; 
v_reuseFailAlloc_5212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5212_, 0, v_a_5206_);
v___x_5211_ = v_reuseFailAlloc_5212_;
goto v_reusejp_5210_;
}
v_reusejp_5210_:
{
return v___x_5211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_){
_start:
{
lean_object* v_res_5220_; 
v_res_5220_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_);
lean_dec(v_a_5218_);
lean_dec_ref(v_a_5217_);
lean_dec(v_a_5216_);
lean_dec_ref(v_a_5215_);
return v_res_5220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5221_, lean_object* v_R_5222_, lean_object* v_a_5223_, lean_object* v_b_5224_){
_start:
{
lean_object* v___x_5225_; 
v___x_5225_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5223_, v_b_5224_);
return v___x_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5226_, lean_object* v_constName_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
lean_object* v___x_5233_; 
v___x_5233_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5234_, lean_object* v_constName_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v_res_5241_; 
v_res_5241_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5234_, v_constName_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_);
lean_dec(v___y_5239_);
lean_dec_ref(v___y_5238_);
lean_dec(v___y_5237_);
lean_dec_ref(v___y_5236_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5242_, lean_object* v_ref_5243_, lean_object* v_constName_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
lean_object* v___x_5250_; 
v___x_5250_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5243_, v_constName_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
return v___x_5250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5251_, lean_object* v_ref_5252_, lean_object* v_constName_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_){
_start:
{
lean_object* v_res_5259_; 
v_res_5259_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5251_, v_ref_5252_, v_constName_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
lean_dec(v___y_5257_);
lean_dec_ref(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec(v_ref_5252_);
return v_res_5259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5260_, lean_object* v_ref_5261_, lean_object* v_msg_5262_, lean_object* v_declHint_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_){
_start:
{
lean_object* v___x_5269_; 
v___x_5269_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5261_, v_msg_5262_, v_declHint_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
return v___x_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5270_, lean_object* v_ref_5271_, lean_object* v_msg_5272_, lean_object* v_declHint_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_){
_start:
{
lean_object* v_res_5279_; 
v_res_5279_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5270_, v_ref_5271_, v_msg_5272_, v_declHint_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
lean_dec(v___y_5275_);
lean_dec_ref(v___y_5274_);
lean_dec(v_ref_5271_);
return v_res_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5280_, lean_object* v_declHint_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_){
_start:
{
lean_object* v___x_5287_; 
v___x_5287_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5280_, v_declHint_5281_, v___y_5285_);
return v___x_5287_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5288_, lean_object* v_declHint_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
lean_object* v_res_5295_; 
v_res_5295_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5288_, v_declHint_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
lean_dec(v___y_5293_);
lean_dec_ref(v___y_5292_);
lean_dec(v___y_5291_);
lean_dec_ref(v___y_5290_);
return v_res_5295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5296_, lean_object* v_ref_5297_, lean_object* v_msg_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
lean_object* v___x_5304_; 
v___x_5304_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5297_, v_msg_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
return v___x_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5305_, lean_object* v_ref_5306_, lean_object* v_msg_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_){
_start:
{
lean_object* v_res_5313_; 
v_res_5313_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5305_, v_ref_5306_, v_msg_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_);
lean_dec(v___y_5311_);
lean_dec_ref(v___y_5310_);
lean_dec(v___y_5309_);
lean_dec_ref(v___y_5308_);
lean_dec(v_ref_5306_);
return v_res_5313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5314_, lean_object* v_body_5315_, lean_object* v_args2_5316_, lean_object* v_ctorVal_5317_, lean_object* v_args1_5318_, lean_object* v_k_5319_, lean_object* v_arg2_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_){
_start:
{
lean_object* v_res_5326_; 
v_res_5326_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5314_, v_body_5315_, v_args2_5316_, v_ctorVal_5317_, v_args1_5318_, v_k_5319_, v_arg2_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec_ref(v_body_5315_);
lean_dec(v_i_5314_);
return v_res_5326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5327_, lean_object* v_args1_5328_, lean_object* v_k_5329_, lean_object* v_i_5330_, lean_object* v_type_5331_, lean_object* v_args2_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_){
_start:
{
lean_object* v___x_5338_; uint8_t v___x_5339_; 
v___x_5338_ = lean_array_get_size(v_args1_5328_);
v___x_5339_ = lean_nat_dec_lt(v_i_5330_, v___x_5338_);
if (v___x_5339_ == 0)
{
lean_object* v___x_5340_; 
lean_dec_ref(v_type_5331_);
lean_dec(v_i_5330_);
lean_dec_ref(v_args1_5328_);
lean_dec_ref(v_ctorVal_5327_);
lean_inc(v_a_5336_);
lean_inc_ref(v_a_5335_);
lean_inc(v_a_5334_);
lean_inc_ref(v_a_5333_);
v___x_5340_ = lean_apply_6(v_k_5329_, v_args2_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, lean_box(0));
return v___x_5340_;
}
else
{
lean_object* v___x_5341_; 
lean_inc(v_a_5336_);
lean_inc_ref(v_a_5335_);
lean_inc(v_a_5334_);
lean_inc_ref(v_a_5333_);
v___x_5341_ = lean_whnf(v_type_5331_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_);
if (lean_obj_tag(v___x_5341_) == 0)
{
lean_object* v_a_5342_; 
v_a_5342_ = lean_ctor_get(v___x_5341_, 0);
lean_inc(v_a_5342_);
lean_dec_ref(v___x_5341_);
if (lean_obj_tag(v_a_5342_) == 7)
{
lean_object* v_binderName_5343_; lean_object* v_binderType_5344_; lean_object* v_body_5345_; lean_object* v___f_5346_; uint8_t v___x_5347_; uint8_t v___x_5348_; lean_object* v___x_5349_; 
v_binderName_5343_ = lean_ctor_get(v_a_5342_, 0);
lean_inc(v_binderName_5343_);
v_binderType_5344_ = lean_ctor_get(v_a_5342_, 1);
lean_inc_ref(v_binderType_5344_);
v_body_5345_ = lean_ctor_get(v_a_5342_, 2);
lean_inc_ref(v_body_5345_);
lean_dec_ref(v_a_5342_);
v___f_5346_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5346_, 0, v_i_5330_);
lean_closure_set(v___f_5346_, 1, v_body_5345_);
lean_closure_set(v___f_5346_, 2, v_args2_5332_);
lean_closure_set(v___f_5346_, 3, v_ctorVal_5327_);
lean_closure_set(v___f_5346_, 4, v_args1_5328_);
lean_closure_set(v___f_5346_, 5, v_k_5329_);
v___x_5347_ = 1;
v___x_5348_ = 0;
v___x_5349_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5343_, v___x_5347_, v_binderType_5344_, v___f_5346_, v___x_5348_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_);
return v___x_5349_;
}
else
{
lean_object* v_toConstantVal_5350_; lean_object* v_name_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; 
lean_dec(v_a_5342_);
lean_dec_ref(v_args2_5332_);
lean_dec(v_i_5330_);
lean_dec_ref(v_k_5329_);
lean_dec_ref(v_args1_5328_);
v_toConstantVal_5350_ = lean_ctor_get(v_ctorVal_5327_, 0);
lean_inc_ref(v_toConstantVal_5350_);
lean_dec_ref(v_ctorVal_5327_);
v_name_5351_ = lean_ctor_get(v_toConstantVal_5350_, 0);
lean_inc(v_name_5351_);
lean_dec_ref(v_toConstantVal_5350_);
v___x_5352_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5353_ = l_Lean_MessageData_ofName(v_name_5351_);
v___x_5354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5354_, 0, v___x_5352_);
lean_ctor_set(v___x_5354_, 1, v___x_5353_);
v___x_5355_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5356_, 0, v___x_5354_);
lean_ctor_set(v___x_5356_, 1, v___x_5355_);
v___x_5357_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5356_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_);
return v___x_5357_;
}
}
else
{
lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
lean_dec_ref(v_args2_5332_);
lean_dec(v_i_5330_);
lean_dec_ref(v_k_5329_);
lean_dec_ref(v_args1_5328_);
lean_dec_ref(v_ctorVal_5327_);
v_a_5358_ = lean_ctor_get(v___x_5341_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5341_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5360_ = v___x_5341_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5341_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5366_, lean_object* v_body_5367_, lean_object* v_args2_5368_, lean_object* v_ctorVal_5369_, lean_object* v_args1_5370_, lean_object* v_k_5371_, lean_object* v_arg2_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_){
_start:
{
lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; 
v___x_5378_ = lean_unsigned_to_nat(1u);
v___x_5379_ = lean_nat_add(v_i_5366_, v___x_5378_);
v___x_5380_ = lean_expr_instantiate1(v_body_5367_, v_arg2_5372_);
v___x_5381_ = lean_array_push(v_args2_5368_, v_arg2_5372_);
v___x_5382_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5369_, v_args1_5370_, v_k_5371_, v___x_5379_, v___x_5380_, v___x_5381_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_);
return v___x_5382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5383_, lean_object* v_args1_5384_, lean_object* v_k_5385_, lean_object* v_i_5386_, lean_object* v_type_5387_, lean_object* v_args2_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_){
_start:
{
lean_object* v_res_5394_; 
v_res_5394_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5383_, v_args1_5384_, v_k_5385_, v_i_5386_, v_type_5387_, v_args2_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_);
lean_dec(v_a_5392_);
lean_dec_ref(v_a_5391_);
lean_dec(v_a_5390_);
lean_dec_ref(v_a_5389_);
return v_res_5394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5395_, lean_object* v_us_5396_, lean_object* v_args1_5397_, lean_object* v___x_5398_, lean_object* v_numParams_5399_, lean_object* v___x_5400_, lean_object* v_args2_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_){
_start:
{
lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
lean_inc(v_us_5396_);
v___x_5407_ = l_Lean_mkConst(v_name_5395_, v_us_5396_);
lean_inc_ref(v___x_5407_);
v___x_5408_ = l_Lean_mkAppN(v___x_5407_, v_args1_5397_);
v___x_5409_ = l_Lean_mkAppN(v___x_5407_, v_args2_5401_);
lean_inc_ref(v___x_5409_);
lean_inc_ref(v___x_5408_);
v___x_5410_ = l_Lean_Meta_mkEqHEq(v___x_5408_, v___x_5409_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
if (lean_obj_tag(v___x_5410_) == 0)
{
lean_object* v_a_5411_; lean_object* v___x_5412_; uint8_t v___x_5413_; lean_object* v___x_5414_; 
v_a_5411_ = lean_ctor_get(v___x_5410_, 0);
lean_inc(v_a_5411_);
lean_dec_ref(v___x_5410_);
lean_inc_ref_n(v_args2_5401_, 2);
v___x_5412_ = l_Array_toSubarray___redArg(v_args2_5401_, v___x_5398_, v_numParams_5399_);
v___x_5413_ = 1;
v___x_5414_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5397_, v_args2_5401_, v___x_5413_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
if (lean_obj_tag(v___x_5414_) == 0)
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5535_; 
v_a_5415_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5535_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5535_ == 0)
{
v___x_5417_ = v___x_5414_;
v_isShared_5418_ = v_isSharedCheck_5535_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5414_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5535_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5419_; 
v___x_5419_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5415_);
if (lean_obj_tag(v___x_5419_) == 1)
{
lean_object* v_val_5420_; lean_object* v___x_5421_; 
lean_del_object(v___x_5417_);
v_val_5420_ = lean_ctor_get(v___x_5419_, 0);
lean_inc(v_val_5420_);
lean_dec_ref(v___x_5419_);
v___x_5421_ = l_Lean_mkArrow(v_a_5411_, v_val_5420_, v___y_5404_, v___y_5405_);
if (lean_obj_tag(v___x_5421_) == 0)
{
lean_object* v_a_5422_; lean_object* v___x_5423_; 
v_a_5422_ = lean_ctor_get(v___x_5421_, 0);
lean_inc(v_a_5422_);
lean_dec_ref(v___x_5421_);
v___x_5423_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5408_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5514_; 
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5514_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5514_ == 0)
{
v___x_5426_ = v___x_5423_;
v_isShared_5427_ = v_isSharedCheck_5514_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5423_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5514_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
if (lean_obj_tag(v_a_5424_) == 1)
{
lean_object* v_val_5428_; lean_object* v___x_5429_; 
lean_del_object(v___x_5426_);
v_val_5428_ = lean_ctor_get(v_a_5424_, 0);
lean_inc(v_val_5428_);
lean_dec_ref(v_a_5424_);
v___x_5429_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5409_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
if (lean_obj_tag(v___x_5429_) == 0)
{
lean_object* v_a_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5501_; 
v_a_5430_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5501_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5501_ == 0)
{
v___x_5432_ = v___x_5429_;
v_isShared_5433_ = v_isSharedCheck_5501_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_a_5430_);
lean_dec(v___x_5429_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5501_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
if (lean_obj_tag(v_a_5430_) == 1)
{
lean_object* v_val_5434_; lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5496_; 
lean_del_object(v___x_5432_);
v_val_5434_ = lean_ctor_get(v_a_5430_, 0);
v_isSharedCheck_5496_ = !lean_is_exclusive(v_a_5430_);
if (v_isSharedCheck_5496_ == 0)
{
v___x_5436_ = v_a_5430_;
v_isShared_5437_ = v_isSharedCheck_5496_;
goto v_resetjp_5435_;
}
else
{
lean_inc(v_val_5434_);
lean_dec(v_a_5430_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5496_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; uint8_t v___x_5442_; lean_object* v___x_5443_; 
v___x_5438_ = l_Subarray_copy___redArg(v___x_5400_);
v___x_5439_ = l_Array_append___redArg(v___x_5438_, v_val_5428_);
v___x_5440_ = l_Subarray_copy___redArg(v___x_5412_);
v___x_5441_ = l_Array_append___redArg(v___x_5440_, v_val_5434_);
lean_dec(v_val_5434_);
v___x_5442_ = 0;
v___x_5443_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5439_, v___x_5441_, v___x_5442_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
lean_dec_ref(v___x_5439_);
if (lean_obj_tag(v___x_5443_) == 0)
{
lean_object* v_a_5444_; lean_object* v___x_5445_; 
v_a_5444_ = lean_ctor_get(v___x_5443_, 0);
lean_inc(v_a_5444_);
lean_dec_ref(v___x_5443_);
v___x_5445_ = l_Lean_mkArrowN(v_a_5444_, v_a_5422_, v___y_5404_, v___y_5405_);
lean_dec(v_a_5444_);
if (lean_obj_tag(v___x_5445_) == 0)
{
lean_object* v_a_5446_; uint8_t v___x_5447_; lean_object* v___x_5448_; 
v_a_5446_ = lean_ctor_get(v___x_5445_, 0);
lean_inc(v_a_5446_);
lean_dec_ref(v___x_5445_);
v___x_5447_ = 1;
v___x_5448_ = l_Lean_Meta_mkForallFVars(v_args2_5401_, v_a_5446_, v___x_5442_, v___x_5413_, v___x_5413_, v___x_5447_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
lean_dec_ref(v_args2_5401_);
if (lean_obj_tag(v___x_5448_) == 0)
{
lean_object* v_a_5449_; lean_object* v___x_5450_; 
v_a_5449_ = lean_ctor_get(v___x_5448_, 0);
lean_inc(v_a_5449_);
lean_dec_ref(v___x_5448_);
v___x_5450_ = l_Lean_Meta_mkForallFVars(v_args1_5397_, v_a_5449_, v___x_5442_, v___x_5413_, v___x_5413_, v___x_5447_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
if (lean_obj_tag(v___x_5450_) == 0)
{
lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5463_; 
v_a_5451_ = lean_ctor_get(v___x_5450_, 0);
v_isSharedCheck_5463_ = !lean_is_exclusive(v___x_5450_);
if (v_isSharedCheck_5463_ == 0)
{
v___x_5453_ = v___x_5450_;
v_isShared_5454_ = v_isSharedCheck_5463_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v___x_5450_);
v___x_5453_ = lean_box(0);
v_isShared_5454_ = v_isSharedCheck_5463_;
goto v_resetjp_5452_;
}
v_resetjp_5452_:
{
lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5458_; 
v___x_5455_ = lean_array_get_size(v_val_5428_);
lean_dec(v_val_5428_);
v___x_5456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5456_, 0, v_a_5451_);
lean_ctor_set(v___x_5456_, 1, v_us_5396_);
lean_ctor_set(v___x_5456_, 2, v___x_5455_);
if (v_isShared_5437_ == 0)
{
lean_ctor_set(v___x_5436_, 0, v___x_5456_);
v___x_5458_ = v___x_5436_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v___x_5456_);
v___x_5458_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
lean_object* v___x_5460_; 
if (v_isShared_5454_ == 0)
{
lean_ctor_set(v___x_5453_, 0, v___x_5458_);
v___x_5460_ = v___x_5453_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v___x_5458_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
}
else
{
lean_object* v_a_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5471_; 
lean_del_object(v___x_5436_);
lean_dec(v_val_5428_);
lean_dec(v_us_5396_);
v_a_5464_ = lean_ctor_get(v___x_5450_, 0);
v_isSharedCheck_5471_ = !lean_is_exclusive(v___x_5450_);
if (v_isSharedCheck_5471_ == 0)
{
v___x_5466_ = v___x_5450_;
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_a_5464_);
lean_dec(v___x_5450_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5469_; 
if (v_isShared_5467_ == 0)
{
v___x_5469_ = v___x_5466_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5464_);
v___x_5469_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
return v___x_5469_;
}
}
}
}
else
{
lean_object* v_a_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5479_; 
lean_del_object(v___x_5436_);
lean_dec(v_val_5428_);
lean_dec(v_us_5396_);
v_a_5472_ = lean_ctor_get(v___x_5448_, 0);
v_isSharedCheck_5479_ = !lean_is_exclusive(v___x_5448_);
if (v_isSharedCheck_5479_ == 0)
{
v___x_5474_ = v___x_5448_;
v_isShared_5475_ = v_isSharedCheck_5479_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_a_5472_);
lean_dec(v___x_5448_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5479_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
lean_object* v___x_5477_; 
if (v_isShared_5475_ == 0)
{
v___x_5477_ = v___x_5474_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v_a_5472_);
v___x_5477_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
return v___x_5477_;
}
}
}
}
else
{
lean_object* v_a_5480_; lean_object* v___x_5482_; uint8_t v_isShared_5483_; uint8_t v_isSharedCheck_5487_; 
lean_del_object(v___x_5436_);
lean_dec(v_val_5428_);
lean_dec_ref(v_args2_5401_);
lean_dec(v_us_5396_);
v_a_5480_ = lean_ctor_get(v___x_5445_, 0);
v_isSharedCheck_5487_ = !lean_is_exclusive(v___x_5445_);
if (v_isSharedCheck_5487_ == 0)
{
v___x_5482_ = v___x_5445_;
v_isShared_5483_ = v_isSharedCheck_5487_;
goto v_resetjp_5481_;
}
else
{
lean_inc(v_a_5480_);
lean_dec(v___x_5445_);
v___x_5482_ = lean_box(0);
v_isShared_5483_ = v_isSharedCheck_5487_;
goto v_resetjp_5481_;
}
v_resetjp_5481_:
{
lean_object* v___x_5485_; 
if (v_isShared_5483_ == 0)
{
v___x_5485_ = v___x_5482_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_a_5480_);
v___x_5485_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
return v___x_5485_;
}
}
}
}
else
{
lean_object* v_a_5488_; lean_object* v___x_5490_; uint8_t v_isShared_5491_; uint8_t v_isSharedCheck_5495_; 
lean_del_object(v___x_5436_);
lean_dec(v_val_5428_);
lean_dec(v_a_5422_);
lean_dec_ref(v_args2_5401_);
lean_dec(v_us_5396_);
v_a_5488_ = lean_ctor_get(v___x_5443_, 0);
v_isSharedCheck_5495_ = !lean_is_exclusive(v___x_5443_);
if (v_isSharedCheck_5495_ == 0)
{
v___x_5490_ = v___x_5443_;
v_isShared_5491_ = v_isSharedCheck_5495_;
goto v_resetjp_5489_;
}
else
{
lean_inc(v_a_5488_);
lean_dec(v___x_5443_);
v___x_5490_ = lean_box(0);
v_isShared_5491_ = v_isSharedCheck_5495_;
goto v_resetjp_5489_;
}
v_resetjp_5489_:
{
lean_object* v___x_5493_; 
if (v_isShared_5491_ == 0)
{
v___x_5493_ = v___x_5490_;
goto v_reusejp_5492_;
}
else
{
lean_object* v_reuseFailAlloc_5494_; 
v_reuseFailAlloc_5494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5494_, 0, v_a_5488_);
v___x_5493_ = v_reuseFailAlloc_5494_;
goto v_reusejp_5492_;
}
v_reusejp_5492_:
{
return v___x_5493_;
}
}
}
}
}
else
{
lean_object* v___x_5497_; lean_object* v___x_5499_; 
lean_dec(v_a_5430_);
lean_dec(v_val_5428_);
lean_dec(v_a_5422_);
lean_dec_ref(v___x_5412_);
lean_dec_ref(v_args2_5401_);
lean_dec_ref(v___x_5400_);
lean_dec(v_us_5396_);
v___x_5497_ = lean_box(0);
if (v_isShared_5433_ == 0)
{
lean_ctor_set(v___x_5432_, 0, v___x_5497_);
v___x_5499_ = v___x_5432_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v___x_5497_);
v___x_5499_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
return v___x_5499_;
}
}
}
}
else
{
lean_object* v_a_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5509_; 
lean_dec(v_val_5428_);
lean_dec(v_a_5422_);
lean_dec_ref(v___x_5412_);
lean_dec_ref(v_args2_5401_);
lean_dec_ref(v___x_5400_);
lean_dec(v_us_5396_);
v_a_5502_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5509_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5509_ == 0)
{
v___x_5504_ = v___x_5429_;
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_a_5502_);
lean_dec(v___x_5429_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v___x_5507_; 
if (v_isShared_5505_ == 0)
{
v___x_5507_ = v___x_5504_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_a_5502_);
v___x_5507_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
return v___x_5507_;
}
}
}
}
else
{
lean_object* v___x_5510_; lean_object* v___x_5512_; 
lean_dec(v_a_5424_);
lean_dec(v_a_5422_);
lean_dec_ref(v___x_5412_);
lean_dec_ref(v___x_5409_);
lean_dec_ref(v_args2_5401_);
lean_dec_ref(v___x_5400_);
lean_dec(v_us_5396_);
v___x_5510_ = lean_box(0);
if (v_isShared_5427_ == 0)
{
lean_ctor_set(v___x_5426_, 0, v___x_5510_);
v___x_5512_ = v___x_5426_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v___x_5510_);
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
else
{
lean_object* v_a_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5522_; 
lean_dec(v_a_5422_);
lean_dec_ref(v___x_5412_);
lean_dec_ref(v___x_5409_);
lean_dec_ref(v_args2_5401_);
lean_dec_ref(v___x_5400_);
lean_dec(v_us_5396_);
v_a_5515_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5522_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5522_ == 0)
{
v___x_5517_ = v___x_5423_;
v_isShared_5518_ = v_isSharedCheck_5522_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_a_5515_);
lean_dec(v___x_5423_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5522_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5520_; 
if (v_isShared_5518_ == 0)
{
v___x_5520_ = v___x_5517_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v_a_5515_);
v___x_5520_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
return v___x_5520_;
}
}
}
}
else
{
lean_object* v_a_5523_; lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5530_; 
lean_dec_ref(v___x_5412_);
lean_dec_ref(v___x_5409_);
lean_dec_ref(v___x_5408_);
lean_dec_ref(v_args2_5401_);
lean_dec_ref(v___x_5400_);
lean_dec(v_us_5396_);
v_a_5523_ = lean_ctor_get(v___x_5421_, 0);
v_isSharedCheck_5530_ = !lean_is_exclusive(v___x_5421_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5525_ = v___x_5421_;
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
else
{
lean_inc(v_a_5523_);
lean_dec(v___x_5421_);
v___x_5525_ = lean_box(0);
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
v_resetjp_5524_:
{
lean_object* v___x_5528_; 
if (v_isShared_5526_ == 0)
{
v___x_5528_ = v___x_5525_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
else
{
lean_object* v___x_5531_; lean_object* v___x_5533_; 
lean_dec(v___x_5419_);
lean_dec_ref(v___x_5412_);
lean_dec(v_a_5411_);
lean_dec_ref(v___x_5409_);
lean_dec_ref(v___x_5408_);
lean_dec_ref(v_args2_5401_);
lean_dec_ref(v___x_5400_);
lean_dec(v_us_5396_);
v___x_5531_ = lean_box(0);
if (v_isShared_5418_ == 0)
{
lean_ctor_set(v___x_5417_, 0, v___x_5531_);
v___x_5533_ = v___x_5417_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v___x_5531_);
v___x_5533_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
return v___x_5533_;
}
}
}
}
else
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5543_; 
lean_dec_ref(v___x_5412_);
lean_dec(v_a_5411_);
lean_dec_ref(v___x_5409_);
lean_dec_ref(v___x_5408_);
lean_dec_ref(v_args2_5401_);
lean_dec_ref(v___x_5400_);
lean_dec(v_us_5396_);
v_a_5536_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5543_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5543_ == 0)
{
v___x_5538_ = v___x_5414_;
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5414_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5541_; 
if (v_isShared_5539_ == 0)
{
v___x_5541_ = v___x_5538_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_a_5536_);
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
lean_dec_ref(v___x_5409_);
lean_dec_ref(v___x_5408_);
lean_dec_ref(v_args2_5401_);
lean_dec_ref(v___x_5400_);
lean_dec(v_numParams_5399_);
lean_dec(v___x_5398_);
lean_dec(v_us_5396_);
v_a_5544_ = lean_ctor_get(v___x_5410_, 0);
v_isSharedCheck_5551_ = !lean_is_exclusive(v___x_5410_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5546_ = v___x_5410_;
v_isShared_5547_ = v_isSharedCheck_5551_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_a_5544_);
lean_dec(v___x_5410_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5552_, lean_object* v_us_5553_, lean_object* v_args1_5554_, lean_object* v___x_5555_, lean_object* v_numParams_5556_, lean_object* v___x_5557_, lean_object* v_args2_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_){
_start:
{
lean_object* v_res_5564_; 
v_res_5564_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5552_, v_us_5553_, v_args1_5554_, v___x_5555_, v_numParams_5556_, v___x_5557_, v_args2_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_);
lean_dec(v___y_5562_);
lean_dec_ref(v___y_5561_);
lean_dec(v___y_5560_);
lean_dec_ref(v___y_5559_);
lean_dec_ref(v_args1_5554_);
return v_res_5564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5565_, lean_object* v_name_5566_, lean_object* v_us_5567_, lean_object* v_ctorVal_5568_, lean_object* v_a_5569_, lean_object* v_args1_5570_, lean_object* v_x_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_){
_start:
{
lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___f_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5577_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5565_);
lean_inc_ref_n(v_args1_5570_, 3);
v___x_5578_ = l_Array_toSubarray___redArg(v_args1_5570_, v___x_5577_, v_numParams_5565_);
v___f_5579_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5579_, 0, v_name_5566_);
lean_closure_set(v___f_5579_, 1, v_us_5567_);
lean_closure_set(v___f_5579_, 2, v_args1_5570_);
lean_closure_set(v___f_5579_, 3, v___x_5577_);
lean_closure_set(v___f_5579_, 4, v_numParams_5565_);
lean_closure_set(v___f_5579_, 5, v___x_5578_);
v___x_5580_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5581_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5581_, 0, v_ctorVal_5568_);
lean_closure_set(v___x_5581_, 1, v_args1_5570_);
lean_closure_set(v___x_5581_, 2, v___f_5579_);
lean_closure_set(v___x_5581_, 3, v___x_5577_);
lean_closure_set(v___x_5581_, 4, v_a_5569_);
lean_closure_set(v___x_5581_, 5, v___x_5580_);
v___x_5582_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5570_, v___x_5581_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
return v___x_5582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5583_, lean_object* v_name_5584_, lean_object* v_us_5585_, lean_object* v_ctorVal_5586_, lean_object* v_a_5587_, lean_object* v_args1_5588_, lean_object* v_x_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_){
_start:
{
lean_object* v_res_5595_; 
v_res_5595_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5583_, v_name_5584_, v_us_5585_, v_ctorVal_5586_, v_a_5587_, v_args1_5588_, v_x_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_);
lean_dec(v___y_5593_);
lean_dec_ref(v___y_5592_);
lean_dec(v___y_5591_);
lean_dec_ref(v___y_5590_);
lean_dec_ref(v_x_5589_);
return v_res_5595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5596_, lean_object* v_a_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_){
_start:
{
lean_object* v_toConstantVal_5602_; lean_object* v_numParams_5603_; lean_object* v_name_5604_; lean_object* v_levelParams_5605_; lean_object* v_type_5606_; lean_object* v___x_5607_; 
v_toConstantVal_5602_ = lean_ctor_get(v_ctorVal_5596_, 0);
v_numParams_5603_ = lean_ctor_get(v_ctorVal_5596_, 3);
lean_inc(v_numParams_5603_);
v_name_5604_ = lean_ctor_get(v_toConstantVal_5602_, 0);
lean_inc(v_name_5604_);
v_levelParams_5605_ = lean_ctor_get(v_toConstantVal_5602_, 1);
v_type_5606_ = lean_ctor_get(v_toConstantVal_5602_, 2);
lean_inc_ref(v_type_5606_);
v___x_5607_ = l_Lean_Meta_elimOptParam(v_type_5606_, v_a_5599_, v_a_5600_);
if (lean_obj_tag(v___x_5607_) == 0)
{
lean_object* v_a_5608_; lean_object* v___x_5609_; lean_object* v_us_5610_; lean_object* v___f_5611_; uint8_t v___x_5612_; lean_object* v___x_5613_; 
v_a_5608_ = lean_ctor_get(v___x_5607_, 0);
lean_inc_n(v_a_5608_, 2);
lean_dec_ref(v___x_5607_);
v___x_5609_ = lean_box(0);
lean_inc(v_levelParams_5605_);
v_us_5610_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5605_, v___x_5609_);
v___f_5611_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5611_, 0, v_numParams_5603_);
lean_closure_set(v___f_5611_, 1, v_name_5604_);
lean_closure_set(v___f_5611_, 2, v_us_5610_);
lean_closure_set(v___f_5611_, 3, v_ctorVal_5596_);
lean_closure_set(v___f_5611_, 4, v_a_5608_);
v___x_5612_ = 0;
v___x_5613_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5608_, v___f_5611_, v___x_5612_, v_a_5597_, v_a_5598_, v_a_5599_, v_a_5600_);
return v___x_5613_;
}
else
{
lean_object* v_a_5614_; lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5621_; 
lean_dec(v_name_5604_);
lean_dec(v_numParams_5603_);
lean_dec_ref(v_ctorVal_5596_);
v_a_5614_ = lean_ctor_get(v___x_5607_, 0);
v_isSharedCheck_5621_ = !lean_is_exclusive(v___x_5607_);
if (v_isSharedCheck_5621_ == 0)
{
v___x_5616_ = v___x_5607_;
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
else
{
lean_inc(v_a_5614_);
lean_dec(v___x_5607_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
lean_object* v___x_5619_; 
if (v_isShared_5617_ == 0)
{
v___x_5619_ = v___x_5616_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_a_5614_);
v___x_5619_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
return v___x_5619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_){
_start:
{
lean_object* v_res_5628_; 
v_res_5628_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5622_, v_a_5623_, v_a_5624_, v_a_5625_, v_a_5626_);
lean_dec(v_a_5626_);
lean_dec_ref(v_a_5625_);
lean_dec(v_a_5624_);
lean_dec_ref(v_a_5623_);
return v_res_5628_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5630_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5631_ = l_Lean_stringToMessageData(v___x_5630_);
return v___x_5631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_){
_start:
{
lean_object* v_toConstantVal_5638_; lean_object* v_name_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; 
v_toConstantVal_5638_ = lean_ctor_get(v_ctorVal_5632_, 0);
lean_inc_ref(v_toConstantVal_5638_);
lean_dec_ref(v_ctorVal_5632_);
v_name_5639_ = lean_ctor_get(v_toConstantVal_5638_, 0);
lean_inc(v_name_5639_);
lean_dec_ref(v_toConstantVal_5638_);
v___x_5640_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5641_ = l_Lean_MessageData_ofName(v_name_5639_);
v___x_5642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5640_);
lean_ctor_set(v___x_5642_, 1, v___x_5641_);
v___x_5643_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5644_, 0, v___x_5642_);
lean_ctor_set(v___x_5644_, 1, v___x_5643_);
v___x_5645_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5644_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_);
return v___x_5645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_){
_start:
{
lean_object* v_res_5652_; 
v_res_5652_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_);
lean_dec(v_a_5650_);
lean_dec_ref(v_a_5649_);
lean_dec(v_a_5648_);
lean_dec_ref(v_a_5647_);
return v_res_5652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5653_, lean_object* v_ctorVal_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_){
_start:
{
lean_object* v___x_5660_; 
v___x_5660_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5654_, v_a_5655_, v_a_5656_, v_a_5657_, v_a_5658_);
return v___x_5660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5661_, lean_object* v_ctorVal_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_){
_start:
{
lean_object* v_res_5668_; 
v_res_5668_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5661_, v_ctorVal_5662_, v_a_5663_, v_a_5664_, v_a_5665_, v_a_5666_);
lean_dec(v_a_5666_);
lean_dec_ref(v_a_5665_);
lean_dec(v_a_5664_);
lean_dec_ref(v_a_5663_);
return v_res_5668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5674_, size_t v_sz_5675_, size_t v_i_5676_, lean_object* v_bs_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_){
_start:
{
uint8_t v___x_5683_; 
v___x_5683_ = lean_usize_dec_lt(v_i_5676_, v_sz_5675_);
if (v___x_5683_ == 0)
{
lean_object* v___x_5684_; 
lean_dec_ref(v_ctorVal_5674_);
v___x_5684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5684_, 0, v_bs_5677_);
return v___x_5684_;
}
else
{
lean_object* v_v_5685_; lean_object* v___x_5686_; 
v_v_5685_ = lean_array_uget_borrowed(v_bs_5677_, v_i_5676_);
lean_inc(v___y_5681_);
lean_inc_ref(v___y_5680_);
lean_inc(v___y_5679_);
lean_inc_ref(v___y_5678_);
lean_inc(v_v_5685_);
v___x_5686_ = lean_infer_type(v_v_5685_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
if (lean_obj_tag(v___x_5686_) == 0)
{
lean_object* v_a_5687_; lean_object* v___x_5688_; 
v_a_5687_ = lean_ctor_get(v___x_5686_, 0);
lean_inc(v_a_5687_);
lean_dec_ref(v___x_5686_);
v___x_5688_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5687_, v___y_5679_);
if (lean_obj_tag(v___x_5688_) == 0)
{
lean_object* v_a_5689_; lean_object* v___x_5690_; lean_object* v_bs_x27_5691_; lean_object* v_a_5693_; lean_object* v___y_5699_; lean_object* v_lhs_5710_; lean_object* v_rhs_5711_; lean_object* v___x_5713_; uint8_t v___x_5714_; 
v_a_5689_ = lean_ctor_get(v___x_5688_, 0);
lean_inc(v_a_5689_);
lean_dec_ref(v___x_5688_);
v___x_5690_ = lean_unsigned_to_nat(0u);
v_bs_x27_5691_ = lean_array_uset(v_bs_5677_, v_i_5676_, v___x_5690_);
v___x_5713_ = l_Lean_Expr_cleanupAnnotations(v_a_5689_);
v___x_5714_ = l_Lean_Expr_isApp(v___x_5713_);
if (v___x_5714_ == 0)
{
lean_object* v___x_5715_; 
lean_dec_ref(v___x_5713_);
lean_inc_ref(v_ctorVal_5674_);
v___x_5715_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5674_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
v___y_5699_ = v___x_5715_;
goto v___jp_5698_;
}
else
{
lean_object* v_arg_5716_; lean_object* v___x_5717_; uint8_t v___x_5718_; 
v_arg_5716_ = lean_ctor_get(v___x_5713_, 1);
lean_inc_ref(v_arg_5716_);
v___x_5717_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5713_);
v___x_5718_ = l_Lean_Expr_isApp(v___x_5717_);
if (v___x_5718_ == 0)
{
lean_object* v___x_5719_; 
lean_dec_ref(v___x_5717_);
lean_dec_ref(v_arg_5716_);
lean_inc_ref(v_ctorVal_5674_);
v___x_5719_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5674_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
v___y_5699_ = v___x_5719_;
goto v___jp_5698_;
}
else
{
lean_object* v_arg_5720_; lean_object* v___x_5721_; uint8_t v___x_5722_; 
v_arg_5720_ = lean_ctor_get(v___x_5717_, 1);
lean_inc_ref(v_arg_5720_);
v___x_5721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5717_);
v___x_5722_ = l_Lean_Expr_isApp(v___x_5721_);
if (v___x_5722_ == 0)
{
lean_object* v___x_5723_; 
lean_dec_ref(v___x_5721_);
lean_dec_ref(v_arg_5720_);
lean_dec_ref(v_arg_5716_);
lean_inc_ref(v_ctorVal_5674_);
v___x_5723_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5674_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
v___y_5699_ = v___x_5723_;
goto v___jp_5698_;
}
else
{
lean_object* v_arg_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; uint8_t v___x_5727_; 
v_arg_5724_ = lean_ctor_get(v___x_5721_, 1);
lean_inc_ref(v_arg_5724_);
v___x_5725_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5721_);
v___x_5726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5727_ = l_Lean_Expr_isConstOf(v___x_5725_, v___x_5726_);
if (v___x_5727_ == 0)
{
uint8_t v___x_5728_; 
lean_dec_ref(v_arg_5720_);
v___x_5728_ = l_Lean_Expr_isApp(v___x_5725_);
if (v___x_5728_ == 0)
{
lean_object* v___x_5729_; 
lean_dec_ref(v___x_5725_);
lean_dec_ref(v_arg_5724_);
lean_dec_ref(v_arg_5716_);
lean_inc_ref(v_ctorVal_5674_);
v___x_5729_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5674_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
v___y_5699_ = v___x_5729_;
goto v___jp_5698_;
}
else
{
lean_object* v___x_5730_; lean_object* v___x_5731_; uint8_t v___x_5732_; 
v___x_5730_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5725_);
v___x_5731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5732_ = l_Lean_Expr_isConstOf(v___x_5730_, v___x_5731_);
lean_dec_ref(v___x_5730_);
if (v___x_5732_ == 0)
{
lean_object* v___x_5733_; 
lean_dec_ref(v_arg_5724_);
lean_dec_ref(v_arg_5716_);
lean_inc_ref(v_ctorVal_5674_);
v___x_5733_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5674_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
v___y_5699_ = v___x_5733_;
goto v___jp_5698_;
}
else
{
v_lhs_5710_ = v_arg_5724_;
v_rhs_5711_ = v_arg_5716_;
goto v___jp_5709_;
}
}
}
else
{
lean_dec_ref(v___x_5725_);
lean_dec_ref(v_arg_5724_);
v_lhs_5710_ = v_arg_5720_;
v_rhs_5711_ = v_arg_5716_;
goto v___jp_5709_;
}
}
}
}
v___jp_5692_:
{
size_t v___x_5694_; size_t v___x_5695_; lean_object* v___x_5696_; 
v___x_5694_ = ((size_t)1ULL);
v___x_5695_ = lean_usize_add(v_i_5676_, v___x_5694_);
v___x_5696_ = lean_array_uset(v_bs_x27_5691_, v_i_5676_, v_a_5693_);
v_i_5676_ = v___x_5695_;
v_bs_5677_ = v___x_5696_;
goto _start;
}
v___jp_5698_:
{
if (lean_obj_tag(v___y_5699_) == 0)
{
lean_object* v_a_5700_; 
v_a_5700_ = lean_ctor_get(v___y_5699_, 0);
lean_inc(v_a_5700_);
lean_dec_ref(v___y_5699_);
v_a_5693_ = v_a_5700_;
goto v___jp_5692_;
}
else
{
lean_object* v_a_5701_; lean_object* v___x_5703_; uint8_t v_isShared_5704_; uint8_t v_isSharedCheck_5708_; 
lean_dec_ref(v_bs_x27_5691_);
lean_dec_ref(v_ctorVal_5674_);
v_a_5701_ = lean_ctor_get(v___y_5699_, 0);
v_isSharedCheck_5708_ = !lean_is_exclusive(v___y_5699_);
if (v_isSharedCheck_5708_ == 0)
{
v___x_5703_ = v___y_5699_;
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
else
{
lean_inc(v_a_5701_);
lean_dec(v___y_5699_);
v___x_5703_ = lean_box(0);
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
v_resetjp_5702_:
{
lean_object* v___x_5706_; 
if (v_isShared_5704_ == 0)
{
v___x_5706_ = v___x_5703_;
goto v_reusejp_5705_;
}
else
{
lean_object* v_reuseFailAlloc_5707_; 
v_reuseFailAlloc_5707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5707_, 0, v_a_5701_);
v___x_5706_ = v_reuseFailAlloc_5707_;
goto v_reusejp_5705_;
}
v_reusejp_5705_:
{
return v___x_5706_;
}
}
}
}
v___jp_5709_:
{
lean_object* v___x_5712_; 
v___x_5712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5712_, 0, v_lhs_5710_);
lean_ctor_set(v___x_5712_, 1, v_rhs_5711_);
v_a_5693_ = v___x_5712_;
goto v___jp_5692_;
}
}
else
{
lean_object* v_a_5734_; lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5741_; 
lean_dec_ref(v_bs_5677_);
lean_dec_ref(v_ctorVal_5674_);
v_a_5734_ = lean_ctor_get(v___x_5688_, 0);
v_isSharedCheck_5741_ = !lean_is_exclusive(v___x_5688_);
if (v_isSharedCheck_5741_ == 0)
{
v___x_5736_ = v___x_5688_;
v_isShared_5737_ = v_isSharedCheck_5741_;
goto v_resetjp_5735_;
}
else
{
lean_inc(v_a_5734_);
lean_dec(v___x_5688_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5741_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v___x_5739_; 
if (v_isShared_5737_ == 0)
{
v___x_5739_ = v___x_5736_;
goto v_reusejp_5738_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v_a_5734_);
v___x_5739_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5738_;
}
v_reusejp_5738_:
{
return v___x_5739_;
}
}
}
}
else
{
lean_object* v_a_5742_; lean_object* v___x_5744_; uint8_t v_isShared_5745_; uint8_t v_isSharedCheck_5749_; 
lean_dec_ref(v_bs_5677_);
lean_dec_ref(v_ctorVal_5674_);
v_a_5742_ = lean_ctor_get(v___x_5686_, 0);
v_isSharedCheck_5749_ = !lean_is_exclusive(v___x_5686_);
if (v_isSharedCheck_5749_ == 0)
{
v___x_5744_ = v___x_5686_;
v_isShared_5745_ = v_isSharedCheck_5749_;
goto v_resetjp_5743_;
}
else
{
lean_inc(v_a_5742_);
lean_dec(v___x_5686_);
v___x_5744_ = lean_box(0);
v_isShared_5745_ = v_isSharedCheck_5749_;
goto v_resetjp_5743_;
}
v_resetjp_5743_:
{
lean_object* v___x_5747_; 
if (v_isShared_5745_ == 0)
{
v___x_5747_ = v___x_5744_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5748_; 
v_reuseFailAlloc_5748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5748_, 0, v_a_5742_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5750_, lean_object* v_sz_5751_, lean_object* v_i_5752_, lean_object* v_bs_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_){
_start:
{
size_t v_sz_boxed_5759_; size_t v_i_boxed_5760_; lean_object* v_res_5761_; 
v_sz_boxed_5759_ = lean_unbox_usize(v_sz_5751_);
lean_dec(v_sz_5751_);
v_i_boxed_5760_ = lean_unbox_usize(v_i_5752_);
lean_dec(v_i_5752_);
v_res_5761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5750_, v_sz_boxed_5759_, v_i_boxed_5760_, v_bs_5753_, v___y_5754_, v___y_5755_, v___y_5756_, v___y_5757_);
lean_dec(v___y_5757_);
lean_dec_ref(v___y_5756_);
lean_dec(v___y_5755_);
lean_dec_ref(v___y_5754_);
return v_res_5761_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5763_; lean_object* v___x_5764_; 
v___x_5763_ = lean_unsigned_to_nat(0u);
v___x_5764_ = l_Lean_Level_ofNat(v___x_5763_);
return v___x_5764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5765_, lean_object* v_us_5766_, lean_object* v_numIndices_5767_, lean_object* v_xs_5768_, lean_object* v_type_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_){
_start:
{
lean_object* v_toConstantVal_5775_; lean_object* v_induct_5776_; lean_object* v_numParams_5777_; lean_object* v___x_5778_; lean_object* v_noConfusionName_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v_noConfusion_5783_; lean_object* v_noConfusion_5784_; lean_object* v_lower_5786_; lean_object* v_upper_5787_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v_n_5898_; uint8_t v___x_5899_; 
v_toConstantVal_5775_ = lean_ctor_get(v_ctorVal_5765_, 0);
v_induct_5776_ = lean_ctor_get(v_ctorVal_5765_, 1);
v_numParams_5777_ = lean_ctor_get(v_ctorVal_5765_, 3);
v___x_5778_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5776_);
v_noConfusionName_5779_ = l_Lean_Name_str___override(v_induct_5776_, v___x_5778_);
v___x_5780_ = lean_unsigned_to_nat(0u);
v___x_5781_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5782_, 0, v___x_5781_);
lean_ctor_set(v___x_5782_, 1, v_us_5766_);
v_noConfusion_5783_ = l_Lean_mkConst(v_noConfusionName_5779_, v___x_5782_);
v_noConfusion_5784_ = l_Lean_Expr_app___override(v_noConfusion_5783_, v_type_5769_);
v___x_5894_ = lean_array_get_size(v_xs_5768_);
v___x_5895_ = lean_nat_sub(v___x_5894_, v_numParams_5777_);
v___x_5896_ = lean_nat_sub(v___x_5895_, v_numIndices_5767_);
lean_dec(v___x_5895_);
v___x_5897_ = lean_unsigned_to_nat(1u);
v_n_5898_ = lean_nat_sub(v___x_5896_, v___x_5897_);
lean_dec(v___x_5896_);
v___x_5899_ = lean_nat_dec_le(v_n_5898_, v___x_5780_);
if (v___x_5899_ == 0)
{
v_lower_5786_ = v_n_5898_;
v_upper_5787_ = v___x_5894_;
goto v___jp_5785_;
}
else
{
lean_dec(v_n_5898_);
v_lower_5786_ = v___x_5780_;
v_upper_5787_ = v___x_5894_;
goto v___jp_5785_;
}
v___jp_5785_:
{
lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v_eqs_5790_; size_t v_sz_5791_; size_t v___x_5792_; lean_object* v___x_5793_; 
lean_inc_ref(v_xs_5768_);
v___x_5788_ = l_Array_toSubarray___redArg(v_xs_5768_, v_lower_5786_, v_upper_5787_);
v___x_5789_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5790_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5788_, v___x_5789_);
v_sz_5791_ = lean_array_size(v_eqs_5790_);
v___x_5792_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5790_);
lean_inc_ref(v_ctorVal_5765_);
v___x_5793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5765_, v_sz_5791_, v___x_5792_, v_eqs_5790_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
if (lean_obj_tag(v___x_5793_) == 0)
{
lean_object* v_a_5794_; lean_object* v___x_5795_; lean_object* v_fst_5796_; lean_object* v_snd_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; 
v_a_5794_ = lean_ctor_get(v___x_5793_, 0);
lean_inc(v_a_5794_);
lean_dec_ref(v___x_5793_);
v___x_5795_ = l_Array_unzip___redArg(v_a_5794_);
lean_dec(v_a_5794_);
v_fst_5796_ = lean_ctor_get(v___x_5795_, 0);
lean_inc(v_fst_5796_);
v_snd_5797_ = lean_ctor_get(v___x_5795_, 1);
lean_inc(v_snd_5797_);
lean_dec_ref(v___x_5795_);
v___x_5798_ = l_Lean_mkAppN(v_noConfusion_5784_, v_fst_5796_);
lean_dec(v_fst_5796_);
v___x_5799_ = l_Lean_mkAppN(v___x_5798_, v_snd_5797_);
lean_dec(v_snd_5797_);
v___x_5800_ = l_Lean_mkAppN(v___x_5799_, v_eqs_5790_);
lean_dec_ref(v_eqs_5790_);
lean_inc(v___y_5773_);
lean_inc_ref(v___y_5772_);
lean_inc(v___y_5771_);
lean_inc_ref(v___y_5770_);
lean_inc_ref(v___x_5800_);
v___x_5801_ = lean_infer_type(v___x_5800_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
if (lean_obj_tag(v___x_5801_) == 0)
{
lean_object* v_a_5802_; lean_object* v___x_5803_; 
v_a_5802_ = lean_ctor_get(v___x_5801_, 0);
lean_inc(v_a_5802_);
lean_dec_ref(v___x_5801_);
lean_inc(v___y_5773_);
lean_inc_ref(v___y_5772_);
lean_inc(v___y_5771_);
lean_inc_ref(v___y_5770_);
v___x_5803_ = lean_whnf(v_a_5802_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
if (lean_obj_tag(v___x_5803_) == 0)
{
lean_object* v_a_5804_; 
v_a_5804_ = lean_ctor_get(v___x_5803_, 0);
lean_inc(v_a_5804_);
lean_dec_ref(v___x_5803_);
if (lean_obj_tag(v_a_5804_) == 7)
{
lean_object* v_binderType_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; 
lean_inc_ref(v_toConstantVal_5775_);
lean_dec_ref(v_ctorVal_5765_);
v_binderType_5805_ = lean_ctor_get(v_a_5804_, 1);
lean_inc_ref(v_binderType_5805_);
lean_dec_ref(v_a_5804_);
v___x_5806_ = lean_box(0);
v___x_5807_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5805_, v___x_5806_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
if (lean_obj_tag(v___x_5807_) == 0)
{
lean_object* v_a_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; 
v_a_5808_ = lean_ctor_get(v___x_5807_, 0);
lean_inc(v_a_5808_);
lean_dec_ref(v___x_5807_);
v___x_5809_ = l_Lean_Expr_mvarId_x21(v_a_5808_);
v___x_5810_ = l_Lean_MVarId_intros(v___x_5809_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v_a_5811_; lean_object* v_snd_5812_; lean_object* v_name_5813_; lean_object* v___x_5814_; 
v_a_5811_ = lean_ctor_get(v___x_5810_, 0);
lean_inc(v_a_5811_);
lean_dec_ref(v___x_5810_);
v_snd_5812_ = lean_ctor_get(v_a_5811_, 1);
lean_inc(v_snd_5812_);
lean_dec(v_a_5811_);
v_name_5813_ = lean_ctor_get(v_toConstantVal_5775_, 0);
lean_inc(v_name_5813_);
lean_dec_ref(v_toConstantVal_5775_);
v___x_5814_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5812_, v_name_5813_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
if (lean_obj_tag(v___x_5814_) == 0)
{
lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v_a_5817_; lean_object* v___x_5819_; uint8_t v_isShared_5820_; uint8_t v_isSharedCheck_5844_; 
lean_dec_ref(v___x_5814_);
v___x_5815_ = l_Lean_Expr_app___override(v___x_5800_, v_a_5808_);
v___x_5816_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5815_, v___y_5771_);
v_a_5817_ = lean_ctor_get(v___x_5816_, 0);
v_isSharedCheck_5844_ = !lean_is_exclusive(v___x_5816_);
if (v_isSharedCheck_5844_ == 0)
{
v___x_5819_ = v___x_5816_;
v_isShared_5820_ = v_isSharedCheck_5844_;
goto v_resetjp_5818_;
}
else
{
lean_inc(v_a_5817_);
lean_dec(v___x_5816_);
v___x_5819_ = lean_box(0);
v_isShared_5820_ = v_isSharedCheck_5844_;
goto v_resetjp_5818_;
}
v_resetjp_5818_:
{
uint8_t v___x_5821_; uint8_t v___x_5822_; uint8_t v___x_5823_; lean_object* v___x_5824_; 
v___x_5821_ = 0;
v___x_5822_ = 1;
v___x_5823_ = 1;
v___x_5824_ = l_Lean_Meta_mkLambdaFVars(v_xs_5768_, v_a_5817_, v___x_5821_, v___x_5822_, v___x_5821_, v___x_5822_, v___x_5823_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
lean_dec_ref(v_xs_5768_);
if (lean_obj_tag(v___x_5824_) == 0)
{
lean_object* v_a_5825_; lean_object* v___x_5827_; uint8_t v_isShared_5828_; uint8_t v_isSharedCheck_5835_; 
v_a_5825_ = lean_ctor_get(v___x_5824_, 0);
v_isSharedCheck_5835_ = !lean_is_exclusive(v___x_5824_);
if (v_isSharedCheck_5835_ == 0)
{
v___x_5827_ = v___x_5824_;
v_isShared_5828_ = v_isSharedCheck_5835_;
goto v_resetjp_5826_;
}
else
{
lean_inc(v_a_5825_);
lean_dec(v___x_5824_);
v___x_5827_ = lean_box(0);
v_isShared_5828_ = v_isSharedCheck_5835_;
goto v_resetjp_5826_;
}
v_resetjp_5826_:
{
lean_object* v___x_5830_; 
if (v_isShared_5820_ == 0)
{
lean_ctor_set_tag(v___x_5819_, 1);
lean_ctor_set(v___x_5819_, 0, v_a_5825_);
v___x_5830_ = v___x_5819_;
goto v_reusejp_5829_;
}
else
{
lean_object* v_reuseFailAlloc_5834_; 
v_reuseFailAlloc_5834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5834_, 0, v_a_5825_);
v___x_5830_ = v_reuseFailAlloc_5834_;
goto v_reusejp_5829_;
}
v_reusejp_5829_:
{
lean_object* v___x_5832_; 
if (v_isShared_5828_ == 0)
{
lean_ctor_set(v___x_5827_, 0, v___x_5830_);
v___x_5832_ = v___x_5827_;
goto v_reusejp_5831_;
}
else
{
lean_object* v_reuseFailAlloc_5833_; 
v_reuseFailAlloc_5833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5833_, 0, v___x_5830_);
v___x_5832_ = v_reuseFailAlloc_5833_;
goto v_reusejp_5831_;
}
v_reusejp_5831_:
{
return v___x_5832_;
}
}
}
}
else
{
lean_object* v_a_5836_; lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5843_; 
lean_del_object(v___x_5819_);
v_a_5836_ = lean_ctor_get(v___x_5824_, 0);
v_isSharedCheck_5843_ = !lean_is_exclusive(v___x_5824_);
if (v_isSharedCheck_5843_ == 0)
{
v___x_5838_ = v___x_5824_;
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
else
{
lean_inc(v_a_5836_);
lean_dec(v___x_5824_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v___x_5841_; 
if (v_isShared_5839_ == 0)
{
v___x_5841_ = v___x_5838_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v_a_5836_);
v___x_5841_ = v_reuseFailAlloc_5842_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
return v___x_5841_;
}
}
}
}
}
else
{
lean_object* v_a_5845_; lean_object* v___x_5847_; uint8_t v_isShared_5848_; uint8_t v_isSharedCheck_5852_; 
lean_dec(v_a_5808_);
lean_dec_ref(v___x_5800_);
lean_dec_ref(v_xs_5768_);
v_a_5845_ = lean_ctor_get(v___x_5814_, 0);
v_isSharedCheck_5852_ = !lean_is_exclusive(v___x_5814_);
if (v_isSharedCheck_5852_ == 0)
{
v___x_5847_ = v___x_5814_;
v_isShared_5848_ = v_isSharedCheck_5852_;
goto v_resetjp_5846_;
}
else
{
lean_inc(v_a_5845_);
lean_dec(v___x_5814_);
v___x_5847_ = lean_box(0);
v_isShared_5848_ = v_isSharedCheck_5852_;
goto v_resetjp_5846_;
}
v_resetjp_5846_:
{
lean_object* v___x_5850_; 
if (v_isShared_5848_ == 0)
{
v___x_5850_ = v___x_5847_;
goto v_reusejp_5849_;
}
else
{
lean_object* v_reuseFailAlloc_5851_; 
v_reuseFailAlloc_5851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5851_, 0, v_a_5845_);
v___x_5850_ = v_reuseFailAlloc_5851_;
goto v_reusejp_5849_;
}
v_reusejp_5849_:
{
return v___x_5850_;
}
}
}
}
else
{
lean_object* v_a_5853_; lean_object* v___x_5855_; uint8_t v_isShared_5856_; uint8_t v_isSharedCheck_5860_; 
lean_dec(v_a_5808_);
lean_dec_ref(v___x_5800_);
lean_dec_ref(v_toConstantVal_5775_);
lean_dec_ref(v_xs_5768_);
v_a_5853_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5860_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5860_ == 0)
{
v___x_5855_ = v___x_5810_;
v_isShared_5856_ = v_isSharedCheck_5860_;
goto v_resetjp_5854_;
}
else
{
lean_inc(v_a_5853_);
lean_dec(v___x_5810_);
v___x_5855_ = lean_box(0);
v_isShared_5856_ = v_isSharedCheck_5860_;
goto v_resetjp_5854_;
}
v_resetjp_5854_:
{
lean_object* v___x_5858_; 
if (v_isShared_5856_ == 0)
{
v___x_5858_ = v___x_5855_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_a_5853_);
v___x_5858_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5857_;
}
v_reusejp_5857_:
{
return v___x_5858_;
}
}
}
}
else
{
lean_object* v_a_5861_; lean_object* v___x_5863_; uint8_t v_isShared_5864_; uint8_t v_isSharedCheck_5868_; 
lean_dec_ref(v___x_5800_);
lean_dec_ref(v_toConstantVal_5775_);
lean_dec_ref(v_xs_5768_);
v_a_5861_ = lean_ctor_get(v___x_5807_, 0);
v_isSharedCheck_5868_ = !lean_is_exclusive(v___x_5807_);
if (v_isSharedCheck_5868_ == 0)
{
v___x_5863_ = v___x_5807_;
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
else
{
lean_inc(v_a_5861_);
lean_dec(v___x_5807_);
v___x_5863_ = lean_box(0);
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
v_resetjp_5862_:
{
lean_object* v___x_5866_; 
if (v_isShared_5864_ == 0)
{
v___x_5866_ = v___x_5863_;
goto v_reusejp_5865_;
}
else
{
lean_object* v_reuseFailAlloc_5867_; 
v_reuseFailAlloc_5867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_a_5861_);
v___x_5866_ = v_reuseFailAlloc_5867_;
goto v_reusejp_5865_;
}
v_reusejp_5865_:
{
return v___x_5866_;
}
}
}
}
else
{
lean_object* v___x_5869_; 
lean_dec(v_a_5804_);
lean_dec_ref(v___x_5800_);
lean_dec_ref(v_xs_5768_);
v___x_5869_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5765_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
return v___x_5869_;
}
}
else
{
lean_object* v_a_5870_; lean_object* v___x_5872_; uint8_t v_isShared_5873_; uint8_t v_isSharedCheck_5877_; 
lean_dec_ref(v___x_5800_);
lean_dec_ref(v_xs_5768_);
lean_dec_ref(v_ctorVal_5765_);
v_a_5870_ = lean_ctor_get(v___x_5803_, 0);
v_isSharedCheck_5877_ = !lean_is_exclusive(v___x_5803_);
if (v_isSharedCheck_5877_ == 0)
{
v___x_5872_ = v___x_5803_;
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
else
{
lean_inc(v_a_5870_);
lean_dec(v___x_5803_);
v___x_5872_ = lean_box(0);
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
v_resetjp_5871_:
{
lean_object* v___x_5875_; 
if (v_isShared_5873_ == 0)
{
v___x_5875_ = v___x_5872_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_a_5870_);
v___x_5875_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
return v___x_5875_;
}
}
}
}
else
{
lean_object* v_a_5878_; lean_object* v___x_5880_; uint8_t v_isShared_5881_; uint8_t v_isSharedCheck_5885_; 
lean_dec_ref(v___x_5800_);
lean_dec_ref(v_xs_5768_);
lean_dec_ref(v_ctorVal_5765_);
v_a_5878_ = lean_ctor_get(v___x_5801_, 0);
v_isSharedCheck_5885_ = !lean_is_exclusive(v___x_5801_);
if (v_isSharedCheck_5885_ == 0)
{
v___x_5880_ = v___x_5801_;
v_isShared_5881_ = v_isSharedCheck_5885_;
goto v_resetjp_5879_;
}
else
{
lean_inc(v_a_5878_);
lean_dec(v___x_5801_);
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
else
{
lean_object* v_a_5886_; lean_object* v___x_5888_; uint8_t v_isShared_5889_; uint8_t v_isSharedCheck_5893_; 
lean_dec_ref(v_eqs_5790_);
lean_dec_ref(v_noConfusion_5784_);
lean_dec_ref(v_xs_5768_);
lean_dec_ref(v_ctorVal_5765_);
v_a_5886_ = lean_ctor_get(v___x_5793_, 0);
v_isSharedCheck_5893_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5893_ == 0)
{
v___x_5888_ = v___x_5793_;
v_isShared_5889_ = v_isSharedCheck_5893_;
goto v_resetjp_5887_;
}
else
{
lean_inc(v_a_5886_);
lean_dec(v___x_5793_);
v___x_5888_ = lean_box(0);
v_isShared_5889_ = v_isSharedCheck_5893_;
goto v_resetjp_5887_;
}
v_resetjp_5887_:
{
lean_object* v___x_5891_; 
if (v_isShared_5889_ == 0)
{
v___x_5891_ = v___x_5888_;
goto v_reusejp_5890_;
}
else
{
lean_object* v_reuseFailAlloc_5892_; 
v_reuseFailAlloc_5892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5892_, 0, v_a_5886_);
v___x_5891_ = v_reuseFailAlloc_5892_;
goto v_reusejp_5890_;
}
v_reusejp_5890_:
{
return v___x_5891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5900_, lean_object* v_us_5901_, lean_object* v_numIndices_5902_, lean_object* v_xs_5903_, lean_object* v_type_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_){
_start:
{
lean_object* v_res_5910_; 
v_res_5910_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5900_, v_us_5901_, v_numIndices_5902_, v_xs_5903_, v_type_5904_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_);
lean_dec(v___y_5908_);
lean_dec_ref(v___y_5907_);
lean_dec(v___y_5906_);
lean_dec_ref(v___y_5905_);
lean_dec(v_numIndices_5902_);
return v_res_5910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5911_, lean_object* v_typeInfo_5912_, lean_object* v_a_5913_, lean_object* v_a_5914_, lean_object* v_a_5915_, lean_object* v_a_5916_){
_start:
{
lean_object* v_thmType_5918_; lean_object* v_us_5919_; lean_object* v_numIndices_5920_; lean_object* v___f_5921_; uint8_t v___x_5922_; lean_object* v___x_5923_; 
v_thmType_5918_ = lean_ctor_get(v_typeInfo_5912_, 0);
lean_inc_ref(v_thmType_5918_);
v_us_5919_ = lean_ctor_get(v_typeInfo_5912_, 1);
lean_inc(v_us_5919_);
v_numIndices_5920_ = lean_ctor_get(v_typeInfo_5912_, 2);
lean_inc(v_numIndices_5920_);
lean_dec_ref(v_typeInfo_5912_);
v___f_5921_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5921_, 0, v_ctorVal_5911_);
lean_closure_set(v___f_5921_, 1, v_us_5919_);
lean_closure_set(v___f_5921_, 2, v_numIndices_5920_);
v___x_5922_ = 0;
v___x_5923_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5918_, v___f_5921_, v___x_5922_, v___x_5922_, v_a_5913_, v_a_5914_, v_a_5915_, v_a_5916_);
return v___x_5923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5924_, lean_object* v_typeInfo_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_, lean_object* v_a_5928_, lean_object* v_a_5929_, lean_object* v_a_5930_){
_start:
{
lean_object* v_res_5931_; 
v_res_5931_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5924_, v_typeInfo_5925_, v_a_5926_, v_a_5927_, v_a_5928_, v_a_5929_);
lean_dec(v_a_5929_);
lean_dec_ref(v_a_5928_);
lean_dec(v_a_5927_);
lean_dec_ref(v_a_5926_);
return v_res_5931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_5934_){
_start:
{
lean_object* v___x_5935_; lean_object* v___x_5936_; 
v___x_5935_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_5936_ = l_Lean_Name_str___override(v_ctorName_5934_, v___x_5935_);
return v___x_5936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_5937_, lean_object* v_ctorVal_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_, lean_object* v_a_5941_, lean_object* v_a_5942_){
_start:
{
lean_object* v___x_5944_; 
lean_inc_ref(v_ctorVal_5938_);
v___x_5944_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5938_, v_a_5939_, v_a_5940_, v_a_5941_, v_a_5942_);
if (lean_obj_tag(v___x_5944_) == 0)
{
lean_object* v_a_5945_; lean_object* v___x_5947_; uint8_t v_isShared_5948_; uint8_t v_isSharedCheck_6006_; 
v_a_5945_ = lean_ctor_get(v___x_5944_, 0);
v_isSharedCheck_6006_ = !lean_is_exclusive(v___x_5944_);
if (v_isSharedCheck_6006_ == 0)
{
v___x_5947_ = v___x_5944_;
v_isShared_5948_ = v_isSharedCheck_6006_;
goto v_resetjp_5946_;
}
else
{
lean_inc(v_a_5945_);
lean_dec(v___x_5944_);
v___x_5947_ = lean_box(0);
v_isShared_5948_ = v_isSharedCheck_6006_;
goto v_resetjp_5946_;
}
v_resetjp_5946_:
{
if (lean_obj_tag(v_a_5945_) == 1)
{
lean_object* v_val_5949_; lean_object* v___x_5950_; 
lean_del_object(v___x_5947_);
v_val_5949_ = lean_ctor_get(v_a_5945_, 0);
lean_inc_n(v_val_5949_, 2);
lean_dec_ref(v_a_5945_);
lean_inc_ref(v_ctorVal_5938_);
v___x_5950_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5938_, v_val_5949_, v_a_5939_, v_a_5940_, v_a_5941_, v_a_5942_);
if (lean_obj_tag(v___x_5950_) == 0)
{
lean_object* v_a_5951_; lean_object* v___x_5953_; uint8_t v_isShared_5954_; uint8_t v_isSharedCheck_5993_; 
v_a_5951_ = lean_ctor_get(v___x_5950_, 0);
v_isSharedCheck_5993_ = !lean_is_exclusive(v___x_5950_);
if (v_isSharedCheck_5993_ == 0)
{
v___x_5953_ = v___x_5950_;
v_isShared_5954_ = v_isSharedCheck_5993_;
goto v_resetjp_5952_;
}
else
{
lean_inc(v_a_5951_);
lean_dec(v___x_5950_);
v___x_5953_ = lean_box(0);
v_isShared_5954_ = v_isSharedCheck_5993_;
goto v_resetjp_5952_;
}
v_resetjp_5952_:
{
if (lean_obj_tag(v_a_5951_) == 1)
{
lean_object* v_toConstantVal_5955_; lean_object* v_val_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_5988_; 
v_toConstantVal_5955_ = lean_ctor_get(v_ctorVal_5938_, 0);
lean_inc_ref(v_toConstantVal_5955_);
lean_dec_ref(v_ctorVal_5938_);
v_val_5956_ = lean_ctor_get(v_a_5951_, 0);
v_isSharedCheck_5988_ = !lean_is_exclusive(v_a_5951_);
if (v_isSharedCheck_5988_ == 0)
{
v___x_5958_ = v_a_5951_;
v_isShared_5959_ = v_isSharedCheck_5988_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_val_5956_);
lean_dec(v_a_5951_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_5988_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v_levelParams_5960_; lean_object* v___x_5962_; uint8_t v_isShared_5963_; uint8_t v_isSharedCheck_5985_; 
v_levelParams_5960_ = lean_ctor_get(v_toConstantVal_5955_, 1);
v_isSharedCheck_5985_ = !lean_is_exclusive(v_toConstantVal_5955_);
if (v_isSharedCheck_5985_ == 0)
{
lean_object* v_unused_5986_; lean_object* v_unused_5987_; 
v_unused_5986_ = lean_ctor_get(v_toConstantVal_5955_, 2);
lean_dec(v_unused_5986_);
v_unused_5987_ = lean_ctor_get(v_toConstantVal_5955_, 0);
lean_dec(v_unused_5987_);
v___x_5962_ = v_toConstantVal_5955_;
v_isShared_5963_ = v_isSharedCheck_5985_;
goto v_resetjp_5961_;
}
else
{
lean_inc(v_levelParams_5960_);
lean_dec(v_toConstantVal_5955_);
v___x_5962_ = lean_box(0);
v_isShared_5963_ = v_isSharedCheck_5985_;
goto v_resetjp_5961_;
}
v_resetjp_5961_:
{
lean_object* v_thmType_5964_; lean_object* v___x_5966_; uint8_t v_isShared_5967_; uint8_t v_isSharedCheck_5982_; 
v_thmType_5964_ = lean_ctor_get(v_val_5949_, 0);
v_isSharedCheck_5982_ = !lean_is_exclusive(v_val_5949_);
if (v_isSharedCheck_5982_ == 0)
{
lean_object* v_unused_5983_; lean_object* v_unused_5984_; 
v_unused_5983_ = lean_ctor_get(v_val_5949_, 2);
lean_dec(v_unused_5983_);
v_unused_5984_ = lean_ctor_get(v_val_5949_, 1);
lean_dec(v_unused_5984_);
v___x_5966_ = v_val_5949_;
v_isShared_5967_ = v_isSharedCheck_5982_;
goto v_resetjp_5965_;
}
else
{
lean_inc(v_thmType_5964_);
lean_dec(v_val_5949_);
v___x_5966_ = lean_box(0);
v_isShared_5967_ = v_isSharedCheck_5982_;
goto v_resetjp_5965_;
}
v_resetjp_5965_:
{
lean_object* v___x_5969_; 
lean_inc(v_thmName_5937_);
if (v_isShared_5963_ == 0)
{
lean_ctor_set(v___x_5962_, 2, v_thmType_5964_);
lean_ctor_set(v___x_5962_, 0, v_thmName_5937_);
v___x_5969_ = v___x_5962_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5981_; 
v_reuseFailAlloc_5981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5981_, 0, v_thmName_5937_);
lean_ctor_set(v_reuseFailAlloc_5981_, 1, v_levelParams_5960_);
lean_ctor_set(v_reuseFailAlloc_5981_, 2, v_thmType_5964_);
v___x_5969_ = v_reuseFailAlloc_5981_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5973_; 
v___x_5970_ = lean_box(0);
v___x_5971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5971_, 0, v_thmName_5937_);
lean_ctor_set(v___x_5971_, 1, v___x_5970_);
if (v_isShared_5967_ == 0)
{
lean_ctor_set(v___x_5966_, 2, v___x_5971_);
lean_ctor_set(v___x_5966_, 1, v_val_5956_);
lean_ctor_set(v___x_5966_, 0, v___x_5969_);
v___x_5973_ = v___x_5966_;
goto v_reusejp_5972_;
}
else
{
lean_object* v_reuseFailAlloc_5980_; 
v_reuseFailAlloc_5980_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5980_, 0, v___x_5969_);
lean_ctor_set(v_reuseFailAlloc_5980_, 1, v_val_5956_);
lean_ctor_set(v_reuseFailAlloc_5980_, 2, v___x_5971_);
v___x_5973_ = v_reuseFailAlloc_5980_;
goto v_reusejp_5972_;
}
v_reusejp_5972_:
{
lean_object* v___x_5975_; 
if (v_isShared_5959_ == 0)
{
lean_ctor_set(v___x_5958_, 0, v___x_5973_);
v___x_5975_ = v___x_5958_;
goto v_reusejp_5974_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v___x_5973_);
v___x_5975_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5974_;
}
v_reusejp_5974_:
{
lean_object* v___x_5977_; 
if (v_isShared_5954_ == 0)
{
lean_ctor_set(v___x_5953_, 0, v___x_5975_);
v___x_5977_ = v___x_5953_;
goto v_reusejp_5976_;
}
else
{
lean_object* v_reuseFailAlloc_5978_; 
v_reuseFailAlloc_5978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5978_, 0, v___x_5975_);
v___x_5977_ = v_reuseFailAlloc_5978_;
goto v_reusejp_5976_;
}
v_reusejp_5976_:
{
return v___x_5977_;
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
lean_object* v___x_5989_; lean_object* v___x_5991_; 
lean_dec(v_a_5951_);
lean_dec(v_val_5949_);
lean_dec_ref(v_ctorVal_5938_);
lean_dec(v_thmName_5937_);
v___x_5989_ = lean_box(0);
if (v_isShared_5954_ == 0)
{
lean_ctor_set(v___x_5953_, 0, v___x_5989_);
v___x_5991_ = v___x_5953_;
goto v_reusejp_5990_;
}
else
{
lean_object* v_reuseFailAlloc_5992_; 
v_reuseFailAlloc_5992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5992_, 0, v___x_5989_);
v___x_5991_ = v_reuseFailAlloc_5992_;
goto v_reusejp_5990_;
}
v_reusejp_5990_:
{
return v___x_5991_;
}
}
}
}
else
{
lean_object* v_a_5994_; lean_object* v___x_5996_; uint8_t v_isShared_5997_; uint8_t v_isSharedCheck_6001_; 
lean_dec(v_val_5949_);
lean_dec_ref(v_ctorVal_5938_);
lean_dec(v_thmName_5937_);
v_a_5994_ = lean_ctor_get(v___x_5950_, 0);
v_isSharedCheck_6001_ = !lean_is_exclusive(v___x_5950_);
if (v_isSharedCheck_6001_ == 0)
{
v___x_5996_ = v___x_5950_;
v_isShared_5997_ = v_isSharedCheck_6001_;
goto v_resetjp_5995_;
}
else
{
lean_inc(v_a_5994_);
lean_dec(v___x_5950_);
v___x_5996_ = lean_box(0);
v_isShared_5997_ = v_isSharedCheck_6001_;
goto v_resetjp_5995_;
}
v_resetjp_5995_:
{
lean_object* v___x_5999_; 
if (v_isShared_5997_ == 0)
{
v___x_5999_ = v___x_5996_;
goto v_reusejp_5998_;
}
else
{
lean_object* v_reuseFailAlloc_6000_; 
v_reuseFailAlloc_6000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6000_, 0, v_a_5994_);
v___x_5999_ = v_reuseFailAlloc_6000_;
goto v_reusejp_5998_;
}
v_reusejp_5998_:
{
return v___x_5999_;
}
}
}
}
else
{
lean_object* v___x_6002_; lean_object* v___x_6004_; 
lean_dec(v_a_5945_);
lean_dec_ref(v_ctorVal_5938_);
lean_dec(v_thmName_5937_);
v___x_6002_ = lean_box(0);
if (v_isShared_5948_ == 0)
{
lean_ctor_set(v___x_5947_, 0, v___x_6002_);
v___x_6004_ = v___x_5947_;
goto v_reusejp_6003_;
}
else
{
lean_object* v_reuseFailAlloc_6005_; 
v_reuseFailAlloc_6005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6005_, 0, v___x_6002_);
v___x_6004_ = v_reuseFailAlloc_6005_;
goto v_reusejp_6003_;
}
v_reusejp_6003_:
{
return v___x_6004_;
}
}
}
}
else
{
lean_object* v_a_6007_; lean_object* v___x_6009_; uint8_t v_isShared_6010_; uint8_t v_isSharedCheck_6014_; 
lean_dec_ref(v_ctorVal_5938_);
lean_dec(v_thmName_5937_);
v_a_6007_ = lean_ctor_get(v___x_5944_, 0);
v_isSharedCheck_6014_ = !lean_is_exclusive(v___x_5944_);
if (v_isSharedCheck_6014_ == 0)
{
v___x_6009_ = v___x_5944_;
v_isShared_6010_ = v_isSharedCheck_6014_;
goto v_resetjp_6008_;
}
else
{
lean_inc(v_a_6007_);
lean_dec(v___x_5944_);
v___x_6009_ = lean_box(0);
v_isShared_6010_ = v_isSharedCheck_6014_;
goto v_resetjp_6008_;
}
v_resetjp_6008_:
{
lean_object* v___x_6012_; 
if (v_isShared_6010_ == 0)
{
v___x_6012_ = v___x_6009_;
goto v_reusejp_6011_;
}
else
{
lean_object* v_reuseFailAlloc_6013_; 
v_reuseFailAlloc_6013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_a_6007_);
v___x_6012_ = v_reuseFailAlloc_6013_;
goto v_reusejp_6011_;
}
v_reusejp_6011_:
{
return v___x_6012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6015_, lean_object* v_ctorVal_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_){
_start:
{
lean_object* v_res_6022_; 
v_res_6022_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6015_, v_ctorVal_6016_, v_a_6017_, v_a_6018_, v_a_6019_, v_a_6020_);
lean_dec(v_a_6020_);
lean_dec_ref(v_a_6019_);
lean_dec(v_a_6018_);
lean_dec_ref(v_a_6017_);
return v_res_6022_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6023_, lean_object* v_n_6024_){
_start:
{
if (lean_obj_tag(v_n_6024_) == 1)
{
lean_object* v_pre_6025_; lean_object* v_str_6026_; lean_object* v___x_6027_; uint8_t v___x_6028_; 
v_pre_6025_ = lean_ctor_get(v_n_6024_, 0);
lean_inc(v_pre_6025_);
v_str_6026_ = lean_ctor_get(v_n_6024_, 1);
lean_inc_ref(v_str_6026_);
lean_dec_ref(v_n_6024_);
v___x_6027_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6028_ = lean_string_dec_eq(v_str_6026_, v___x_6027_);
lean_dec_ref(v_str_6026_);
if (v___x_6028_ == 0)
{
lean_dec(v_pre_6025_);
lean_dec_ref(v_env_6023_);
return v___x_6028_;
}
else
{
uint8_t v___x_6029_; lean_object* v___x_6030_; 
v___x_6029_ = 0;
v___x_6030_ = l_Lean_Environment_find_x3f(v_env_6023_, v_pre_6025_, v___x_6029_);
if (lean_obj_tag(v___x_6030_) == 1)
{
lean_object* v_val_6031_; 
v_val_6031_ = lean_ctor_get(v___x_6030_, 0);
lean_inc(v_val_6031_);
lean_dec_ref(v___x_6030_);
if (lean_obj_tag(v_val_6031_) == 6)
{
lean_dec_ref(v_val_6031_);
return v___x_6028_;
}
else
{
lean_dec(v_val_6031_);
return v___x_6029_;
}
}
else
{
lean_dec(v___x_6030_);
return v___x_6029_;
}
}
}
else
{
uint8_t v___x_6032_; 
lean_dec(v_n_6024_);
lean_dec_ref(v_env_6023_);
v___x_6032_ = 0;
return v___x_6032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6033_, lean_object* v_n_6034_){
_start:
{
uint8_t v_res_6035_; lean_object* v_r_6036_; 
v_res_6035_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6033_, v_n_6034_);
v_r_6036_ = lean_box(v_res_6035_);
return v_r_6036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6039_; lean_object* v___x_6040_; 
v___f_6039_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6040_ = l_Lean_registerReservedNamePredicate(v___f_6039_);
return v___x_6040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6041_){
_start:
{
lean_object* v_res_6042_; 
v_res_6042_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6042_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6043_, lean_object* v___y_6044_){
_start:
{
lean_object* v___x_6046_; lean_object* v_env_6047_; lean_object* v_toConstantVal_6048_; lean_object* v_value_6049_; lean_object* v_all_6050_; uint8_t v___y_6052_; lean_object* v_type_6060_; uint8_t v___x_6061_; 
v___x_6046_ = lean_st_ref_get(v___y_6044_);
v_env_6047_ = lean_ctor_get(v___x_6046_, 0);
lean_inc_ref_n(v_env_6047_, 2);
lean_dec(v___x_6046_);
v_toConstantVal_6048_ = lean_ctor_get(v_thm_6043_, 0);
v_value_6049_ = lean_ctor_get(v_thm_6043_, 1);
v_all_6050_ = lean_ctor_get(v_thm_6043_, 2);
v_type_6060_ = lean_ctor_get(v_toConstantVal_6048_, 2);
v___x_6061_ = l_Lean_Environment_hasUnsafe(v_env_6047_, v_type_6060_);
if (v___x_6061_ == 0)
{
uint8_t v___x_6062_; 
v___x_6062_ = l_Lean_Environment_hasUnsafe(v_env_6047_, v_value_6049_);
v___y_6052_ = v___x_6062_;
goto v___jp_6051_;
}
else
{
lean_dec_ref(v_env_6047_);
v___y_6052_ = v___x_6061_;
goto v___jp_6051_;
}
v___jp_6051_:
{
if (v___y_6052_ == 0)
{
lean_object* v___x_6053_; lean_object* v___x_6054_; 
v___x_6053_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6053_, 0, v_thm_6043_);
v___x_6054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6053_);
return v___x_6054_;
}
else
{
lean_object* v___x_6055_; uint8_t v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; 
lean_inc(v_all_6050_);
lean_inc_ref(v_value_6049_);
lean_inc_ref(v_toConstantVal_6048_);
lean_dec_ref(v_thm_6043_);
v___x_6055_ = lean_box(0);
v___x_6056_ = 0;
v___x_6057_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6057_, 0, v_toConstantVal_6048_);
lean_ctor_set(v___x_6057_, 1, v_value_6049_);
lean_ctor_set(v___x_6057_, 2, v___x_6055_);
lean_ctor_set(v___x_6057_, 3, v_all_6050_);
lean_ctor_set_uint8(v___x_6057_, sizeof(void*)*4, v___x_6056_);
v___x_6058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6058_, 0, v___x_6057_);
v___x_6059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6059_, 0, v___x_6058_);
return v___x_6059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6063_, lean_object* v___y_6064_, lean_object* v___y_6065_){
_start:
{
lean_object* v_res_6066_; 
v_res_6066_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6063_, v___y_6064_);
lean_dec(v___y_6064_);
return v_res_6066_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_){
_start:
{
lean_object* v___x_6073_; 
v___x_6073_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6067_, v___y_6071_);
return v___x_6073_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_){
_start:
{
lean_object* v_res_6080_; 
v_res_6080_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_);
lean_dec(v___y_6078_);
lean_dec_ref(v___y_6077_);
lean_dec(v___y_6076_);
lean_dec_ref(v___y_6075_);
return v_res_6080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6081_, uint8_t v___x_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_){
_start:
{
lean_object* v___x_6088_; lean_object* v_a_6089_; lean_object* v___x_6090_; 
v___x_6088_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6081_, v___y_6086_);
v_a_6089_ = lean_ctor_get(v___x_6088_, 0);
lean_inc(v_a_6089_);
lean_dec_ref(v___x_6088_);
v___x_6090_ = l_Lean_addDecl(v_a_6089_, v___x_6082_, v___y_6085_, v___y_6086_);
return v___x_6090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6091_, lean_object* v___x_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_){
_start:
{
uint8_t v___x_2122__boxed_6098_; lean_object* v_res_6099_; 
v___x_2122__boxed_6098_ = lean_unbox(v___x_6092_);
v_res_6099_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6091_, v___x_2122__boxed_6098_, v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_);
lean_dec(v___y_6096_);
lean_dec_ref(v___y_6095_);
lean_dec(v___y_6094_);
lean_dec_ref(v___y_6093_);
return v_res_6099_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; 
v___x_6102_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6103_ = lean_unsigned_to_nat(0u);
v___x_6104_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
lean_ctor_set(v___x_6104_, 1, v___x_6103_);
lean_ctor_set(v___x_6104_, 2, v___x_6103_);
lean_ctor_set(v___x_6104_, 3, v___x_6103_);
lean_ctor_set(v___x_6104_, 4, v___x_6102_);
lean_ctor_set(v___x_6104_, 5, v___x_6102_);
lean_ctor_set(v___x_6104_, 6, v___x_6102_);
lean_ctor_set(v___x_6104_, 7, v___x_6102_);
lean_ctor_set(v___x_6104_, 8, v___x_6102_);
lean_ctor_set(v___x_6104_, 9, v___x_6102_);
return v___x_6104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6105_; lean_object* v___x_6106_; 
v___x_6105_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6106_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6106_, 0, v___x_6105_);
lean_ctor_set(v___x_6106_, 1, v___x_6105_);
lean_ctor_set(v___x_6106_, 2, v___x_6105_);
lean_ctor_set(v___x_6106_, 3, v___x_6105_);
lean_ctor_set(v___x_6106_, 4, v___x_6105_);
lean_ctor_set(v___x_6106_, 5, v___x_6105_);
return v___x_6106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6107_; lean_object* v___x_6108_; 
v___x_6107_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6107_);
lean_ctor_set(v___x_6108_, 1, v___x_6107_);
lean_ctor_set(v___x_6108_, 2, v___x_6107_);
lean_ctor_set(v___x_6108_, 3, v___x_6107_);
lean_ctor_set(v___x_6108_, 4, v___x_6107_);
return v___x_6108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6109_, lean_object* v_name_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_){
_start:
{
if (lean_obj_tag(v_name_6110_) == 1)
{
lean_object* v_pre_6122_; lean_object* v_str_6123_; lean_object* v___x_6124_; uint8_t v___x_6125_; 
v_pre_6122_ = lean_ctor_get(v_name_6110_, 0);
lean_inc(v_pre_6122_);
v_str_6123_ = lean_ctor_get(v_name_6110_, 1);
v___x_6124_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6125_ = lean_string_dec_eq(v_str_6123_, v___x_6124_);
if (v___x_6125_ == 0)
{
lean_dec(v_pre_6122_);
lean_dec_ref(v_name_6110_);
lean_dec(v___x_6109_);
goto v___jp_6118_;
}
else
{
lean_object* v___x_6126_; lean_object* v_env_6127_; uint8_t v___x_6128_; lean_object* v___x_6129_; 
v___x_6126_ = lean_st_ref_get(v___y_6112_);
v_env_6127_ = lean_ctor_get(v___x_6126_, 0);
lean_inc_ref(v_env_6127_);
lean_dec(v___x_6126_);
v___x_6128_ = 0;
lean_inc(v_pre_6122_);
v___x_6129_ = l_Lean_Environment_find_x3f(v_env_6127_, v_pre_6122_, v___x_6128_);
if (lean_obj_tag(v___x_6129_) == 1)
{
lean_object* v_val_6130_; 
v_val_6130_ = lean_ctor_get(v___x_6129_, 0);
lean_inc(v_val_6130_);
lean_dec_ref(v___x_6129_);
if (lean_obj_tag(v_val_6130_) == 6)
{
lean_object* v_val_6131_; lean_object* v___x_6133_; uint8_t v_isShared_6134_; uint8_t v_isSharedCheck_6181_; 
v_val_6131_ = lean_ctor_get(v_val_6130_, 0);
v_isSharedCheck_6181_ = !lean_is_exclusive(v_val_6130_);
if (v_isSharedCheck_6181_ == 0)
{
v___x_6133_ = v_val_6130_;
v_isShared_6134_ = v_isSharedCheck_6181_;
goto v_resetjp_6132_;
}
else
{
lean_inc(v_val_6131_);
lean_dec(v_val_6130_);
v___x_6133_ = lean_box(0);
v_isShared_6134_ = v_isSharedCheck_6181_;
goto v_resetjp_6132_;
}
v_resetjp_6132_:
{
uint8_t v___x_6135_; uint8_t v___x_6136_; uint8_t v___x_6137_; lean_object* v___x_6138_; uint64_t v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; uint8_t v_a_6153_; lean_object* v___x_6159_; 
v___x_6135_ = 1;
v___x_6136_ = 0;
v___x_6137_ = 2;
v___x_6138_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_6138_, 0, v___x_6128_);
lean_ctor_set_uint8(v___x_6138_, 1, v___x_6128_);
lean_ctor_set_uint8(v___x_6138_, 2, v___x_6128_);
lean_ctor_set_uint8(v___x_6138_, 3, v___x_6128_);
lean_ctor_set_uint8(v___x_6138_, 4, v___x_6128_);
lean_ctor_set_uint8(v___x_6138_, 5, v___x_6125_);
lean_ctor_set_uint8(v___x_6138_, 6, v___x_6125_);
lean_ctor_set_uint8(v___x_6138_, 7, v___x_6128_);
lean_ctor_set_uint8(v___x_6138_, 8, v___x_6125_);
lean_ctor_set_uint8(v___x_6138_, 9, v___x_6135_);
lean_ctor_set_uint8(v___x_6138_, 10, v___x_6136_);
lean_ctor_set_uint8(v___x_6138_, 11, v___x_6125_);
lean_ctor_set_uint8(v___x_6138_, 12, v___x_6125_);
lean_ctor_set_uint8(v___x_6138_, 13, v___x_6125_);
lean_ctor_set_uint8(v___x_6138_, 14, v___x_6137_);
lean_ctor_set_uint8(v___x_6138_, 15, v___x_6125_);
lean_ctor_set_uint8(v___x_6138_, 16, v___x_6125_);
lean_ctor_set_uint8(v___x_6138_, 17, v___x_6125_);
lean_ctor_set_uint8(v___x_6138_, 18, v___x_6125_);
v___x_6139_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6138_);
v___x_6140_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6140_, 0, v___x_6138_);
lean_ctor_set_uint64(v___x_6140_, sizeof(void*)*1, v___x_6139_);
v___x_6141_ = lean_unsigned_to_nat(0u);
v___x_6142_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6143_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6144_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6145_ = lean_box(0);
lean_inc(v___x_6109_);
v___x_6146_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6146_, 0, v___x_6140_);
lean_ctor_set(v___x_6146_, 1, v___x_6109_);
lean_ctor_set(v___x_6146_, 2, v___x_6143_);
lean_ctor_set(v___x_6146_, 3, v___x_6144_);
lean_ctor_set(v___x_6146_, 4, v___x_6145_);
lean_ctor_set(v___x_6146_, 5, v___x_6141_);
lean_ctor_set(v___x_6146_, 6, v___x_6145_);
lean_ctor_set_uint8(v___x_6146_, sizeof(void*)*7, v___x_6128_);
lean_ctor_set_uint8(v___x_6146_, sizeof(void*)*7 + 1, v___x_6128_);
lean_ctor_set_uint8(v___x_6146_, sizeof(void*)*7 + 2, v___x_6128_);
lean_ctor_set_uint8(v___x_6146_, sizeof(void*)*7 + 3, v___x_6125_);
v___x_6147_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6148_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6149_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6150_, 0, v___x_6147_);
lean_ctor_set(v___x_6150_, 1, v___x_6148_);
lean_ctor_set(v___x_6150_, 2, v___x_6109_);
lean_ctor_set(v___x_6150_, 3, v___x_6142_);
lean_ctor_set(v___x_6150_, 4, v___x_6149_);
v___x_6151_ = lean_st_mk_ref(v___x_6150_);
lean_inc_ref(v_name_6110_);
v___x_6159_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6110_, v_val_6131_, v___x_6146_, v___x_6151_, v___y_6111_, v___y_6112_);
if (lean_obj_tag(v___x_6159_) == 0)
{
lean_object* v_a_6160_; 
v_a_6160_ = lean_ctor_get(v___x_6159_, 0);
lean_inc(v_a_6160_);
lean_dec_ref(v___x_6159_);
if (lean_obj_tag(v_a_6160_) == 1)
{
lean_object* v_val_6161_; lean_object* v___x_6162_; lean_object* v___f_6163_; lean_object* v___x_6164_; 
v_val_6161_ = lean_ctor_get(v_a_6160_, 0);
lean_inc(v_val_6161_);
lean_dec_ref(v_a_6160_);
v___x_6162_ = lean_box(v___x_6128_);
v___f_6163_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6163_, 0, v_val_6161_);
lean_closure_set(v___f_6163_, 1, v___x_6162_);
v___x_6164_ = l_Lean_Meta_realizeConst(v_pre_6122_, v_name_6110_, v___f_6163_, v___x_6146_, v___x_6151_, v___y_6111_, v___y_6112_);
lean_dec_ref(v___x_6146_);
if (lean_obj_tag(v___x_6164_) == 0)
{
lean_dec_ref(v___x_6164_);
v_a_6153_ = v___x_6125_;
goto v___jp_6152_;
}
else
{
lean_object* v_a_6165_; lean_object* v___x_6167_; uint8_t v_isShared_6168_; uint8_t v_isSharedCheck_6172_; 
lean_dec(v___x_6151_);
lean_del_object(v___x_6133_);
v_a_6165_ = lean_ctor_get(v___x_6164_, 0);
v_isSharedCheck_6172_ = !lean_is_exclusive(v___x_6164_);
if (v_isSharedCheck_6172_ == 0)
{
v___x_6167_ = v___x_6164_;
v_isShared_6168_ = v_isSharedCheck_6172_;
goto v_resetjp_6166_;
}
else
{
lean_inc(v_a_6165_);
lean_dec(v___x_6164_);
v___x_6167_ = lean_box(0);
v_isShared_6168_ = v_isSharedCheck_6172_;
goto v_resetjp_6166_;
}
v_resetjp_6166_:
{
lean_object* v___x_6170_; 
if (v_isShared_6168_ == 0)
{
v___x_6170_ = v___x_6167_;
goto v_reusejp_6169_;
}
else
{
lean_object* v_reuseFailAlloc_6171_; 
v_reuseFailAlloc_6171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6171_, 0, v_a_6165_);
v___x_6170_ = v_reuseFailAlloc_6171_;
goto v_reusejp_6169_;
}
v_reusejp_6169_:
{
return v___x_6170_;
}
}
}
}
else
{
lean_dec(v_a_6160_);
lean_dec_ref(v___x_6146_);
lean_dec(v_pre_6122_);
lean_dec_ref(v_name_6110_);
v_a_6153_ = v___x_6128_;
goto v___jp_6152_;
}
}
else
{
lean_object* v_a_6173_; lean_object* v___x_6175_; uint8_t v_isShared_6176_; uint8_t v_isSharedCheck_6180_; 
lean_dec(v___x_6151_);
lean_dec_ref(v___x_6146_);
lean_del_object(v___x_6133_);
lean_dec_ref(v_name_6110_);
lean_dec(v_pre_6122_);
v_a_6173_ = lean_ctor_get(v___x_6159_, 0);
v_isSharedCheck_6180_ = !lean_is_exclusive(v___x_6159_);
if (v_isSharedCheck_6180_ == 0)
{
v___x_6175_ = v___x_6159_;
v_isShared_6176_ = v_isSharedCheck_6180_;
goto v_resetjp_6174_;
}
else
{
lean_inc(v_a_6173_);
lean_dec(v___x_6159_);
v___x_6175_ = lean_box(0);
v_isShared_6176_ = v_isSharedCheck_6180_;
goto v_resetjp_6174_;
}
v_resetjp_6174_:
{
lean_object* v___x_6178_; 
if (v_isShared_6176_ == 0)
{
v___x_6178_ = v___x_6175_;
goto v_reusejp_6177_;
}
else
{
lean_object* v_reuseFailAlloc_6179_; 
v_reuseFailAlloc_6179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6179_, 0, v_a_6173_);
v___x_6178_ = v_reuseFailAlloc_6179_;
goto v_reusejp_6177_;
}
v_reusejp_6177_:
{
return v___x_6178_;
}
}
}
v___jp_6152_:
{
lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6157_; 
v___x_6154_ = lean_st_ref_get(v___x_6151_);
lean_dec(v___x_6151_);
lean_dec(v___x_6154_);
v___x_6155_ = lean_box(v_a_6153_);
if (v_isShared_6134_ == 0)
{
lean_ctor_set_tag(v___x_6133_, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6155_);
v___x_6157_ = v___x_6133_;
goto v_reusejp_6156_;
}
else
{
lean_object* v_reuseFailAlloc_6158_; 
v_reuseFailAlloc_6158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6158_, 0, v___x_6155_);
v___x_6157_ = v_reuseFailAlloc_6158_;
goto v_reusejp_6156_;
}
v_reusejp_6156_:
{
return v___x_6157_;
}
}
}
}
else
{
lean_dec(v_val_6130_);
lean_dec(v_pre_6122_);
lean_dec_ref(v_name_6110_);
lean_dec(v___x_6109_);
goto v___jp_6114_;
}
}
else
{
lean_dec(v___x_6129_);
lean_dec(v_pre_6122_);
lean_dec_ref(v_name_6110_);
lean_dec(v___x_6109_);
goto v___jp_6114_;
}
}
}
else
{
lean_dec(v_name_6110_);
lean_dec(v___x_6109_);
goto v___jp_6118_;
}
v___jp_6114_:
{
uint8_t v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; 
v___x_6115_ = 0;
v___x_6116_ = lean_box(v___x_6115_);
v___x_6117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6116_);
return v___x_6117_;
}
v___jp_6118_:
{
uint8_t v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; 
v___x_6119_ = 0;
v___x_6120_ = lean_box(v___x_6119_);
v___x_6121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6120_);
return v___x_6121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6182_, lean_object* v_name_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_){
_start:
{
lean_object* v_res_6187_; 
v_res_6187_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6182_, v_name_6183_, v___y_6184_, v___y_6185_);
lean_dec(v___y_6185_);
lean_dec_ref(v___y_6184_);
return v_res_6187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6191_; lean_object* v___x_6192_; 
v___f_6191_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6192_ = l_Lean_registerReservedNameAction(v___f_6191_);
return v___x_6192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6193_){
_start:
{
lean_object* v_res_6194_; 
v_res_6194_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6194_;
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
