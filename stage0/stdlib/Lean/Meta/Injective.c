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
lean_object* v___y_246_; lean_object* v_fileName_255_; lean_object* v_fileMap_256_; lean_object* v_options_257_; lean_object* v_currRecDepth_258_; lean_object* v_maxRecDepth_259_; lean_object* v_ref_260_; lean_object* v_currNamespace_261_; lean_object* v_openDecls_262_; lean_object* v_initHeartbeats_263_; lean_object* v_maxHeartbeats_264_; lean_object* v_quotContext_265_; lean_object* v_currMacroScope_266_; uint8_t v_diag_267_; lean_object* v_cancelTk_x3f_268_; uint8_t v_suppressElabErrors_269_; lean_object* v_inheritedTraceOptions_270_; uint8_t v___x_271_; 
v_fileName_255_ = lean_ctor_get(v___y_242_, 0);
lean_inc_ref(v_fileName_255_);
v_fileMap_256_ = lean_ctor_get(v___y_242_, 1);
lean_inc_ref(v_fileMap_256_);
v_options_257_ = lean_ctor_get(v___y_242_, 2);
lean_inc_ref(v_options_257_);
v_currRecDepth_258_ = lean_ctor_get(v___y_242_, 3);
lean_inc(v_currRecDepth_258_);
v_maxRecDepth_259_ = lean_ctor_get(v___y_242_, 4);
lean_inc(v_maxRecDepth_259_);
v_ref_260_ = lean_ctor_get(v___y_242_, 5);
lean_inc(v_ref_260_);
v_currNamespace_261_ = lean_ctor_get(v___y_242_, 6);
lean_inc(v_currNamespace_261_);
v_openDecls_262_ = lean_ctor_get(v___y_242_, 7);
lean_inc(v_openDecls_262_);
v_initHeartbeats_263_ = lean_ctor_get(v___y_242_, 8);
lean_inc(v_initHeartbeats_263_);
v_maxHeartbeats_264_ = lean_ctor_get(v___y_242_, 9);
lean_inc(v_maxHeartbeats_264_);
v_quotContext_265_ = lean_ctor_get(v___y_242_, 10);
lean_inc(v_quotContext_265_);
v_currMacroScope_266_ = lean_ctor_get(v___y_242_, 11);
lean_inc(v_currMacroScope_266_);
v_diag_267_ = lean_ctor_get_uint8(v___y_242_, sizeof(void*)*14);
v_cancelTk_x3f_268_ = lean_ctor_get(v___y_242_, 12);
lean_inc(v_cancelTk_x3f_268_);
v_suppressElabErrors_269_ = lean_ctor_get_uint8(v___y_242_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_270_ = lean_ctor_get(v___y_242_, 13);
lean_inc_ref(v_inheritedTraceOptions_270_);
lean_dec_ref(v___y_242_);
v___x_271_ = lean_nat_dec_eq(v_currRecDepth_258_, v_maxRecDepth_259_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v_currRecDepth_258_, v___x_272_);
lean_dec(v_currRecDepth_258_);
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
else
{
lean_object* v___x_276_; 
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
lean_dec_ref(v_x_240_);
v___x_276_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_260_);
v___y_246_ = v___x_276_;
goto v___jp_245_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec(v___y_278_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_283_, lean_object* v_x_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_apply_1(v_x_284_, lean_box(0));
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_290_, lean_object* v_x_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(v_00_u03b1_290_, v_x_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_296_, lean_object* v_x_297_){
_start:
{
if (lean_obj_tag(v_x_297_) == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_box(0);
return v___x_298_;
}
else
{
lean_object* v_key_299_; lean_object* v_value_300_; lean_object* v_tail_301_; uint8_t v___x_302_; 
v_key_299_ = lean_ctor_get(v_x_297_, 0);
v_value_300_ = lean_ctor_get(v_x_297_, 1);
v_tail_301_ = lean_ctor_get(v_x_297_, 2);
v___x_302_ = l_Lean_ExprStructEq_beq(v_key_299_, v_a_296_);
if (v___x_302_ == 0)
{
v_x_297_ = v_tail_301_;
goto _start;
}
else
{
lean_object* v___x_304_; 
lean_inc(v_value_300_);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v_value_300_);
return v___x_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_305_, lean_object* v_x_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_305_, v_x_306_);
lean_dec(v_x_306_);
lean_dec_ref(v_a_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(lean_object* v_m_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_buckets_310_; lean_object* v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v_fold_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_buckets_310_ = lean_ctor_get(v_m_308_, 1);
v___x_311_ = lean_array_get_size(v_buckets_310_);
v___x_312_ = l_Lean_ExprStructEq_hash(v_a_309_);
v___x_313_ = 32ULL;
v___x_314_ = lean_uint64_shift_right(v___x_312_, v___x_313_);
v_fold_315_ = lean_uint64_xor(v___x_312_, v___x_314_);
v___x_316_ = 16ULL;
v___x_317_ = lean_uint64_shift_right(v_fold_315_, v___x_316_);
v___x_318_ = lean_uint64_xor(v_fold_315_, v___x_317_);
v___x_319_ = lean_uint64_to_usize(v___x_318_);
v___x_320_ = lean_usize_of_nat(v___x_311_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_sub(v___x_320_, v___x_321_);
v___x_323_ = lean_usize_land(v___x_319_, v___x_322_);
v___x_324_ = lean_array_uget_borrowed(v_buckets_310_, v___x_323_);
v___x_325_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_309_, v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_326_, v_a_327_);
lean_dec_ref(v_a_327_);
lean_dec_ref(v_m_326_);
return v_res_328_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_329_; lean_object* v_dummy_330_; 
v___x_329_ = lean_box(0);
v_dummy_330_ = l_Lean_Expr_sort___override(v___x_329_);
return v_dummy_330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(lean_object* v_pre_331_, lean_object* v_post_332_, size_t v_sz_333_, size_t v_i_334_, lean_object* v_bs_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
uint8_t v___x_340_; 
v___x_340_ = lean_usize_dec_lt(v_i_334_, v_sz_333_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec_ref(v_post_332_);
lean_dec_ref(v_pre_331_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v_bs_335_);
return v___x_341_;
}
else
{
lean_object* v_v_342_; lean_object* v___x_343_; 
v_v_342_ = lean_array_uget_borrowed(v_bs_335_, v_i_334_);
lean_inc(v_v_342_);
lean_inc_ref(v_post_332_);
lean_inc_ref(v_pre_331_);
v___x_343_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_331_, v_post_332_, v_v_342_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_345_; lean_object* v_bs_x27_346_; size_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref(v___x_343_);
v___x_345_ = lean_unsigned_to_nat(0u);
v_bs_x27_346_ = lean_array_uset(v_bs_335_, v_i_334_, v___x_345_);
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_add(v_i_334_, v___x_347_);
v___x_349_ = lean_array_uset(v_bs_x27_346_, v_i_334_, v_a_344_);
v_i_334_ = v___x_348_;
v_bs_335_ = v___x_349_;
goto _start;
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref(v_bs_335_);
lean_dec_ref(v_post_332_);
lean_dec_ref(v_pre_331_);
v_a_351_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_343_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_343_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(lean_object* v_pre_359_, lean_object* v_post_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
if (lean_obj_tag(v_x_361_) == 5)
{
lean_object* v_fn_368_; lean_object* v_arg_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_fn_368_ = lean_ctor_get(v_x_361_, 0);
lean_inc_ref(v_fn_368_);
v_arg_369_ = lean_ctor_get(v_x_361_, 1);
lean_inc_ref(v_arg_369_);
lean_dec_ref(v_x_361_);
v___x_370_ = lean_array_set(v_x_362_, v_x_363_, v_arg_369_);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_sub(v_x_363_, v___x_371_);
lean_dec(v_x_363_);
v_x_361_ = v_fn_368_;
v_x_362_ = v___x_370_;
v_x_363_ = v___x_372_;
goto _start;
}
else
{
lean_object* v___x_374_; 
lean_dec(v_x_363_);
lean_inc_ref(v_post_360_);
lean_inc_ref(v_pre_359_);
v___x_374_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_359_, v_post_360_, v_x_361_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; size_t v_sz_376_; size_t v___x_377_; lean_object* v___x_378_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref(v___x_374_);
v_sz_376_ = lean_array_size(v_x_362_);
v___x_377_ = ((size_t)0ULL);
lean_inc_ref(v_post_360_);
lean_inc_ref(v_pre_359_);
v___x_378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_359_, v_post_360_, v_sz_376_, v___x_377_, v_x_362_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref(v___x_378_);
v___x_380_ = l_Lean_mkAppN(v_a_375_, v_a_379_);
lean_dec(v_a_379_);
v___x_381_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_359_, v_post_360_, v___x_380_, v___y_364_, v___y_365_, v___y_366_);
return v___x_381_;
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_a_375_);
lean_dec_ref(v_post_360_);
lean_dec_ref(v_pre_359_);
v_a_382_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_378_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_378_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_dec_ref(v_x_362_);
lean_dec_ref(v_post_360_);
lean_dec_ref(v_pre_359_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(lean_object* v_pre_390_, lean_object* v_e_391_, lean_object* v_post_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; uint8_t v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; uint8_t v___y_405_; lean_object* v___y_415_; uint8_t v___y_416_; lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; uint8_t v___y_420_; lean_object* v___y_428_; lean_object* v___y_429_; lean_object* v___y_430_; uint8_t v___y_431_; lean_object* v___y_432_; uint8_t v___y_433_; lean_object* v___x_440_; 
lean_inc_ref(v_pre_390_);
lean_inc(v___y_395_);
lean_inc_ref(v___y_394_);
lean_inc_ref(v_e_391_);
v___x_440_ = lean_apply_4(v_pre_390_, v_e_391_, v___y_394_, v___y_395_, lean_box(0));
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_530_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_530_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_530_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_530_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___y_446_; 
switch(lean_obj_tag(v_a_441_))
{
case 0:
{
lean_object* v_e_520_; lean_object* v___x_522_; 
lean_dec_ref(v_post_392_);
lean_dec_ref(v_e_391_);
lean_dec_ref(v_pre_390_);
v_e_520_ = lean_ctor_get(v_a_441_, 0);
lean_inc_ref(v_e_520_);
lean_dec_ref(v_a_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v_e_520_);
v___x_522_ = v___x_443_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_e_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
case 1:
{
lean_object* v_e_524_; lean_object* v___x_525_; 
lean_del_object(v___x_443_);
lean_dec_ref(v_e_391_);
v_e_524_ = lean_ctor_get(v_a_441_, 0);
lean_inc_ref(v_e_524_);
lean_dec_ref(v_a_441_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_e_524_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref(v___x_525_);
v___x_527_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v_a_526_, v___y_393_, v___y_394_, v___y_395_);
return v___x_527_;
}
else
{
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_525_;
}
}
default: 
{
lean_object* v_e_x3f_528_; 
lean_del_object(v___x_443_);
v_e_x3f_528_ = lean_ctor_get(v_a_441_, 0);
lean_inc(v_e_x3f_528_);
lean_dec_ref(v_a_441_);
if (lean_obj_tag(v_e_x3f_528_) == 0)
{
v___y_446_ = v_e_391_;
goto v___jp_445_;
}
else
{
lean_object* v_val_529_; 
lean_dec_ref(v_e_391_);
v_val_529_ = lean_ctor_get(v_e_x3f_528_, 0);
lean_inc(v_val_529_);
lean_dec_ref(v_e_x3f_528_);
v___y_446_ = v_val_529_;
goto v___jp_445_;
}
}
}
v___jp_445_:
{
switch(lean_obj_tag(v___y_446_))
{
case 7:
{
lean_object* v_binderName_447_; lean_object* v_binderType_448_; lean_object* v_body_449_; uint8_t v_binderInfo_450_; lean_object* v___x_451_; 
v_binderName_447_ = lean_ctor_get(v___y_446_, 0);
lean_inc(v_binderName_447_);
v_binderType_448_ = lean_ctor_get(v___y_446_, 1);
v_body_449_ = lean_ctor_get(v___y_446_, 2);
v_binderInfo_450_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_448_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_binderType_448_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref(v___x_451_);
lean_inc_ref(v_body_449_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_453_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_body_449_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; size_t v___x_455_; size_t v___x_456_; uint8_t v___x_457_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref(v___x_453_);
v___x_455_ = lean_ptr_addr(v_binderType_448_);
v___x_456_ = lean_ptr_addr(v_a_452_);
v___x_457_ = lean_usize_dec_eq(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
v___y_428_ = v_a_454_;
v___y_429_ = v_a_452_;
v___y_430_ = v___y_446_;
v___y_431_ = v_binderInfo_450_;
v___y_432_ = v_binderName_447_;
v___y_433_ = v___x_457_;
goto v___jp_427_;
}
else
{
size_t v___x_458_; size_t v___x_459_; uint8_t v___x_460_; 
v___x_458_ = lean_ptr_addr(v_body_449_);
v___x_459_ = lean_ptr_addr(v_a_454_);
v___x_460_ = lean_usize_dec_eq(v___x_458_, v___x_459_);
v___y_428_ = v_a_454_;
v___y_429_ = v_a_452_;
v___y_430_ = v___y_446_;
v___y_431_ = v_binderInfo_450_;
v___y_432_ = v_binderName_447_;
v___y_433_ = v___x_460_;
goto v___jp_427_;
}
}
else
{
lean_dec(v_a_452_);
lean_dec(v_binderName_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_453_;
}
}
else
{
lean_dec(v_binderName_447_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_451_;
}
}
case 6:
{
lean_object* v_binderName_461_; lean_object* v_binderType_462_; lean_object* v_body_463_; uint8_t v_binderInfo_464_; lean_object* v___x_465_; 
v_binderName_461_ = lean_ctor_get(v___y_446_, 0);
lean_inc(v_binderName_461_);
v_binderType_462_ = lean_ctor_get(v___y_446_, 1);
v_body_463_ = lean_ctor_get(v___y_446_, 2);
v_binderInfo_464_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_462_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_465_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_binderType_462_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref(v___x_465_);
lean_inc_ref(v_body_463_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_467_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_body_463_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; size_t v___x_469_; size_t v___x_470_; uint8_t v___x_471_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref(v___x_467_);
v___x_469_ = lean_ptr_addr(v_binderType_462_);
v___x_470_ = lean_ptr_addr(v_a_466_);
v___x_471_ = lean_usize_dec_eq(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
v___y_415_ = v_binderName_461_;
v___y_416_ = v_binderInfo_464_;
v___y_417_ = v_a_468_;
v___y_418_ = v_a_466_;
v___y_419_ = v___y_446_;
v___y_420_ = v___x_471_;
goto v___jp_414_;
}
else
{
size_t v___x_472_; size_t v___x_473_; uint8_t v___x_474_; 
v___x_472_ = lean_ptr_addr(v_body_463_);
v___x_473_ = lean_ptr_addr(v_a_468_);
v___x_474_ = lean_usize_dec_eq(v___x_472_, v___x_473_);
v___y_415_ = v_binderName_461_;
v___y_416_ = v_binderInfo_464_;
v___y_417_ = v_a_468_;
v___y_418_ = v_a_466_;
v___y_419_ = v___y_446_;
v___y_420_ = v___x_474_;
goto v___jp_414_;
}
}
else
{
lean_dec(v_a_466_);
lean_dec_ref(v___y_446_);
lean_dec(v_binderName_461_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_467_;
}
}
else
{
lean_dec_ref(v___y_446_);
lean_dec(v_binderName_461_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_465_;
}
}
case 8:
{
lean_object* v_declName_475_; lean_object* v_type_476_; lean_object* v_value_477_; lean_object* v_body_478_; uint8_t v_nondep_479_; lean_object* v___x_480_; 
v_declName_475_ = lean_ctor_get(v___y_446_, 0);
lean_inc(v_declName_475_);
v_type_476_ = lean_ctor_get(v___y_446_, 1);
v_value_477_ = lean_ctor_get(v___y_446_, 2);
v_body_478_ = lean_ctor_get(v___y_446_, 3);
lean_inc_ref(v_body_478_);
v_nondep_479_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_476_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_type_476_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref(v___x_480_);
lean_inc_ref(v_value_477_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_482_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_value_477_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_484_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref(v___x_482_);
lean_inc_ref(v_body_478_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_484_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_body_478_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; size_t v___x_486_; size_t v___x_487_; uint8_t v___x_488_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref(v___x_484_);
v___x_486_ = lean_ptr_addr(v_type_476_);
v___x_487_ = lean_ptr_addr(v_a_481_);
v___x_488_ = lean_usize_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
v___y_398_ = v_a_481_;
v___y_399_ = v_body_478_;
v___y_400_ = v_a_483_;
v___y_401_ = v___y_446_;
v___y_402_ = v_nondep_479_;
v___y_403_ = v_a_485_;
v___y_404_ = v_declName_475_;
v___y_405_ = v___x_488_;
goto v___jp_397_;
}
else
{
size_t v___x_489_; size_t v___x_490_; uint8_t v___x_491_; 
v___x_489_ = lean_ptr_addr(v_value_477_);
v___x_490_ = lean_ptr_addr(v_a_483_);
v___x_491_ = lean_usize_dec_eq(v___x_489_, v___x_490_);
v___y_398_ = v_a_481_;
v___y_399_ = v_body_478_;
v___y_400_ = v_a_483_;
v___y_401_ = v___y_446_;
v___y_402_ = v_nondep_479_;
v___y_403_ = v_a_485_;
v___y_404_ = v_declName_475_;
v___y_405_ = v___x_491_;
goto v___jp_397_;
}
}
else
{
lean_dec(v_a_483_);
lean_dec(v_a_481_);
lean_dec_ref(v_body_478_);
lean_dec_ref(v___y_446_);
lean_dec(v_declName_475_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_484_;
}
}
else
{
lean_dec(v_a_481_);
lean_dec_ref(v_body_478_);
lean_dec_ref(v___y_446_);
lean_dec(v_declName_475_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_482_;
}
}
else
{
lean_dec_ref(v_body_478_);
lean_dec(v_declName_475_);
lean_dec_ref(v___y_446_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_480_;
}
}
case 5:
{
lean_object* v_dummy_492_; lean_object* v_nargs_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_dummy_492_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_493_ = l_Lean_Expr_getAppNumArgs(v___y_446_);
lean_inc(v_nargs_493_);
v___x_494_ = lean_mk_array(v_nargs_493_, v_dummy_492_);
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_nat_sub(v_nargs_493_, v___x_495_);
lean_dec(v_nargs_493_);
v___x_497_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_390_, v_post_392_, v___y_446_, v___x_494_, v___x_496_, v___y_393_, v___y_394_, v___y_395_);
return v___x_497_;
}
case 10:
{
lean_object* v_data_498_; lean_object* v_expr_499_; lean_object* v___x_500_; 
v_data_498_ = lean_ctor_get(v___y_446_, 0);
v_expr_499_ = lean_ctor_get(v___y_446_, 1);
lean_inc_ref(v_expr_499_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_500_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_expr_499_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; size_t v___x_502_; size_t v___x_503_; uint8_t v___x_504_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref(v___x_500_);
v___x_502_ = lean_ptr_addr(v_expr_499_);
v___x_503_ = lean_ptr_addr(v_a_501_);
v___x_504_ = lean_usize_dec_eq(v___x_502_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_inc(v_data_498_);
lean_dec_ref(v___y_446_);
v___x_505_ = l_Lean_Expr_mdata___override(v_data_498_, v_a_501_);
v___x_506_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_505_, v___y_393_, v___y_394_, v___y_395_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; 
lean_dec(v_a_501_);
v___x_507_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___y_446_, v___y_393_, v___y_394_, v___y_395_);
return v___x_507_;
}
}
else
{
lean_dec_ref(v___y_446_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_500_;
}
}
case 11:
{
lean_object* v_typeName_508_; lean_object* v_idx_509_; lean_object* v_struct_510_; lean_object* v___x_511_; 
v_typeName_508_ = lean_ctor_get(v___y_446_, 0);
v_idx_509_ = lean_ctor_get(v___y_446_, 1);
v_struct_510_ = lean_ctor_get(v___y_446_, 2);
lean_inc_ref(v_struct_510_);
lean_inc_ref(v_post_392_);
lean_inc_ref(v_pre_390_);
v___x_511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_390_, v_post_392_, v_struct_510_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref(v___x_511_);
v___x_513_ = lean_ptr_addr(v_struct_510_);
v___x_514_ = lean_ptr_addr(v_a_512_);
v___x_515_ = lean_usize_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_inc(v_idx_509_);
lean_inc(v_typeName_508_);
lean_dec_ref(v___y_446_);
v___x_516_ = l_Lean_Expr_proj___override(v_typeName_508_, v_idx_509_, v_a_512_);
v___x_517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_516_, v___y_393_, v___y_394_, v___y_395_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; 
lean_dec(v_a_512_);
v___x_518_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___y_446_, v___y_393_, v___y_394_, v___y_395_);
return v___x_518_;
}
}
else
{
lean_dec_ref(v___y_446_);
lean_dec_ref(v_post_392_);
lean_dec_ref(v_pre_390_);
return v___x_511_;
}
}
default: 
{
lean_object* v___x_519_; 
v___x_519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___y_446_, v___y_393_, v___y_394_, v___y_395_);
return v___x_519_;
}
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v_post_392_);
lean_dec_ref(v_e_391_);
lean_dec_ref(v_pre_390_);
v_a_531_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_440_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_440_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
v___jp_397_:
{
if (v___y_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec_ref(v___y_401_);
lean_dec_ref(v___y_399_);
v___x_406_ = l_Lean_Expr_letE___override(v___y_404_, v___y_398_, v___y_400_, v___y_403_, v___y_402_);
v___x_407_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_406_, v___y_393_, v___y_394_, v___y_395_);
return v___x_407_;
}
else
{
size_t v___x_408_; size_t v___x_409_; uint8_t v___x_410_; 
v___x_408_ = lean_ptr_addr(v___y_399_);
lean_dec_ref(v___y_399_);
v___x_409_ = lean_ptr_addr(v___y_403_);
v___x_410_ = lean_usize_dec_eq(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v___y_401_);
v___x_411_ = l_Lean_Expr_letE___override(v___y_404_, v___y_398_, v___y_400_, v___y_403_, v___y_402_);
v___x_412_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_411_, v___y_393_, v___y_394_, v___y_395_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; 
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec_ref(v___y_400_);
lean_dec_ref(v___y_398_);
v___x_413_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___y_401_, v___y_393_, v___y_394_, v___y_395_);
return v___x_413_;
}
}
}
v___jp_414_:
{
if (v___y_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec_ref(v___y_419_);
v___x_421_ = l_Lean_Expr_lam___override(v___y_415_, v___y_418_, v___y_417_, v___y_416_);
v___x_422_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_421_, v___y_393_, v___y_394_, v___y_395_);
return v___x_422_;
}
else
{
uint8_t v___x_423_; 
v___x_423_ = l_Lean_instBEqBinderInfo_beq(v___y_416_, v___y_416_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref(v___y_419_);
v___x_424_ = l_Lean_Expr_lam___override(v___y_415_, v___y_418_, v___y_417_, v___y_416_);
v___x_425_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_424_, v___y_393_, v___y_394_, v___y_395_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; 
lean_dec_ref(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_415_);
v___x_426_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___y_419_, v___y_393_, v___y_394_, v___y_395_);
return v___x_426_;
}
}
}
v___jp_427_:
{
if (v___y_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref(v___y_430_);
v___x_434_ = l_Lean_Expr_forallE___override(v___y_432_, v___y_429_, v___y_428_, v___y_431_);
v___x_435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_434_, v___y_393_, v___y_394_, v___y_395_);
return v___x_435_;
}
else
{
uint8_t v___x_436_; 
v___x_436_ = l_Lean_instBEqBinderInfo_beq(v___y_431_, v___y_431_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec_ref(v___y_430_);
v___x_437_ = l_Lean_Expr_forallE___override(v___y_432_, v___y_429_, v___y_428_, v___y_431_);
v___x_438_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___x_437_, v___y_393_, v___y_394_, v___y_395_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; 
lean_dec(v___y_432_);
lean_dec_ref(v___y_429_);
lean_dec_ref(v___y_428_);
v___x_439_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_390_, v_post_392_, v___y_430_, v___y_393_, v___y_394_, v___y_395_);
return v___x_439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_539_, lean_object* v_e_540_, lean_object* v_post_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1(v_pre_539_, v_e_540_, v_post_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(lean_object* v_pre_547_, lean_object* v_post_548_, lean_object* v_e_549_, lean_object* v_a_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_inc(v_a_550_);
v___x_554_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_554_, 0, lean_box(0));
lean_closure_set(v___x_554_, 1, lean_box(0));
lean_closure_set(v___x_554_, 2, v_a_550_);
v___x_555_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___x_554_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_586_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_586_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_586_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_586_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_a_556_, v_e_549_);
lean_dec(v_a_556_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___f_561_; lean_object* v___x_562_; 
lean_del_object(v___x_558_);
lean_inc_ref(v_e_549_);
v___f_561_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___boxed), 7, 3);
lean_closure_set(v___f_561_, 0, v_pre_547_);
lean_closure_set(v___f_561_, 1, v_e_549_);
lean_closure_set(v___f_561_, 2, v_post_548_);
lean_inc_ref(v___y_551_);
v___x_562_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v___f_561_, v_a_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___f_564_; lean_object* v___x_565_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref(v___x_562_);
lean_inc(v_a_563_);
lean_inc(v_a_550_);
v___f_564_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_564_, 0, v_a_550_);
lean_closure_set(v___f_564_, 1, v_e_549_);
lean_closure_set(v___f_564_, 2, v_a_563_);
v___x_565_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__0(lean_box(0), v___f_564_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v___x_565_, 0);
lean_dec(v_unused_573_);
v___x_567_ = v___x_565_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_dec(v___x_565_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v_a_563_);
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_563_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec(v_a_563_);
v_a_574_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_565_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_565_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
else
{
lean_dec_ref(v_e_549_);
return v___x_562_;
}
}
else
{
lean_object* v_val_582_; lean_object* v___x_584_; 
lean_dec_ref(v_e_549_);
lean_dec_ref(v_post_548_);
lean_dec_ref(v_pre_547_);
v_val_582_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_val_582_);
lean_dec_ref(v___x_560_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_val_582_);
v___x_584_ = v___x_558_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_val_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v_e_549_);
lean_dec_ref(v_post_548_);
lean_dec_ref(v_pre_547_);
v_a_587_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_555_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_555_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(lean_object* v_pre_595_, lean_object* v_post_596_, lean_object* v_e_597_, lean_object* v_a_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; 
lean_inc_ref(v_post_596_);
lean_inc(v___y_600_);
lean_inc_ref(v___y_599_);
lean_inc_ref(v_e_597_);
v___x_602_ = lean_apply_4(v_post_596_, v_e_597_, v___y_599_, v___y_600_, lean_box(0));
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_621_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_621_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_621_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_621_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
switch(lean_obj_tag(v_a_603_))
{
case 0:
{
lean_object* v_e_607_; lean_object* v___x_609_; 
lean_dec_ref(v_e_597_);
lean_dec_ref(v_post_596_);
lean_dec_ref(v_pre_595_);
v_e_607_ = lean_ctor_get(v_a_603_, 0);
lean_inc_ref(v_e_607_);
lean_dec_ref(v_a_603_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v_e_607_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_e_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
case 1:
{
lean_object* v_e_611_; lean_object* v___x_612_; 
lean_del_object(v___x_605_);
lean_dec_ref(v_e_597_);
v_e_611_ = lean_ctor_get(v_a_603_, 0);
lean_inc_ref(v_e_611_);
lean_dec_ref(v_a_603_);
v___x_612_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_595_, v_post_596_, v_e_611_, v_a_598_, v___y_599_, v___y_600_);
return v___x_612_;
}
default: 
{
lean_object* v_e_x3f_613_; 
lean_dec_ref(v_post_596_);
lean_dec_ref(v_pre_595_);
v_e_x3f_613_ = lean_ctor_get(v_a_603_, 0);
lean_inc(v_e_x3f_613_);
lean_dec_ref(v_a_603_);
if (lean_obj_tag(v_e_x3f_613_) == 0)
{
lean_object* v___x_615_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v_e_597_);
v___x_615_ = v___x_605_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_e_597_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
else
{
lean_object* v_val_617_; lean_object* v___x_619_; 
lean_dec_ref(v_e_597_);
v_val_617_ = lean_ctor_get(v_e_x3f_613_, 0);
lean_inc(v_val_617_);
lean_dec_ref(v_e_x3f_613_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v_val_617_);
v___x_619_ = v___x_605_;
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
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_e_597_);
lean_dec_ref(v_post_596_);
lean_dec_ref(v_pre_595_);
v_a_622_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_602_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_602_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_630_, lean_object* v_post_631_, lean_object* v_e_632_, lean_object* v_a_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__2(v_pre_630_, v_post_631_, v_e_632_, v_a_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v_a_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_638_, lean_object* v_post_639_, lean_object* v_sz_640_, lean_object* v_i_641_, lean_object* v_bs_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
size_t v_sz_boxed_647_; size_t v_i_boxed_648_; lean_object* v_res_649_; 
v_sz_boxed_647_ = lean_unbox_usize(v_sz_640_);
lean_dec(v_sz_640_);
v_i_boxed_648_ = lean_unbox_usize(v_i_641_);
lean_dec(v_i_641_);
v_res_649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__1(v_pre_638_, v_post_639_, v_sz_boxed_647_, v_i_boxed_648_, v_bs_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_650_, lean_object* v_post_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__4(v_pre_650_, v_post_651_, v_x_652_, v_x_653_, v_x_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___boxed(lean_object* v_pre_660_, lean_object* v_post_661_, lean_object* v_e_662_, lean_object* v_a_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_660_, v_post_661_, v_e_662_, v_a_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v_a_663_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_object* v_00_u03b1_668_, lean_object* v_x_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_apply_1(v_x_669_, lean_box(0));
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0___boxed(lean_object* v_00_u03b1_675_, lean_object* v_x_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(v_00_u03b1_675_, v_x_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v_res_680_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = lean_box(0);
v___x_682_ = lean_unsigned_to_nat(16u);
v___x_683_ = lean_mk_array(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__0);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_684_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__1);
v___x_688_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_688_, 0, lean_box(0));
lean_closure_set(v___x_688_, 1, lean_box(0));
lean_closure_set(v___x_688_, 2, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(lean_object* v_input_689_, lean_object* v_pre_690_, lean_object* v_post_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v_a_697_; lean_object* v___x_698_; 
v___x_695_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___closed__2);
v___x_696_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_695_, v___y_692_, v___y_693_);
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref(v___x_696_);
v___x_698_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0(v_pre_690_, v_post_691_, v_input_689_, v_a_697_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v___x_698_);
v___x_700_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_700_, 0, lean_box(0));
lean_closure_set(v___x_700_, 1, lean_box(0));
lean_closure_set(v___x_700_, 2, v_a_697_);
v___x_701_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___lam__0(lean_box(0), v___x_700_, v___y_692_, v___y_693_);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v___x_701_, 0);
lean_dec(v_unused_709_);
v___x_703_ = v___x_701_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_dec(v___x_701_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v_a_699_);
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_699_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_dec(v_a_697_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0___boxed(lean_object* v_input_710_, lean_object* v_pre_711_, lean_object* v_post_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_input_710_, v_pre_711_, v_post_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam(lean_object* v_type_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___f_723_; lean_object* v___f_724_; lean_object* v___x_725_; 
v___f_723_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__0));
v___f_724_ = ((lean_object*)(l_Lean_Meta_elimOptParam___closed__1));
v___x_725_ = l_Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0(v_type_719_, v___f_723_, v___f_724_, v_a_720_, v_a_721_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_elimOptParam___boxed(lean_object* v_type_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Meta_elimOptParam(v_type_726_, v_a_727_, v_a_728_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_731_, lean_object* v_m_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___redArg(v_m_732_, v_a_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_735_, lean_object* v_m_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3(v_00_u03b2_735_, v_m_736_, v_a_737_);
lean_dec_ref(v_a_737_);
lean_dec_ref(v_m_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_739_, lean_object* v_ref_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_740_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_745_, lean_object* v_ref_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_745_, v_ref_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_751_, lean_object* v_x_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
lean_inc_ref(v___y_754_);
v___x_757_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___redArg(v_x_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_758_, lean_object* v_x_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__5(v_00_u03b1_758_, v_x_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_765_, lean_object* v_m_766_, lean_object* v_a_767_, lean_object* v_b_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6___redArg(v_m_766_, v_a_767_, v_b_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_770_, lean_object* v_a_771_, lean_object* v_x_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___redArg(v_a_771_, v_x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_774_, lean_object* v_a_775_, lean_object* v_x_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_774_, v_a_775_, v_x_776_);
lean_dec(v_x_776_);
lean_dec_ref(v_a_775_);
return v_res_777_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_778_, lean_object* v_a_779_, lean_object* v_x_780_){
_start:
{
uint8_t v___x_781_; 
v___x_781_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___redArg(v_a_779_, v_x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_782_, lean_object* v_a_783_, lean_object* v_x_784_){
_start:
{
uint8_t v_res_785_; lean_object* v_r_786_; 
v_res_785_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_782_, v_a_783_, v_x_784_);
lean_dec(v_x_784_);
lean_dec_ref(v_a_783_);
v_r_786_ = lean_box(v_res_785_);
return v_r_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_787_, lean_object* v_data_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10___redArg(v_data_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_790_, lean_object* v_a_791_, lean_object* v_b_792_, lean_object* v_x_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__11___redArg(v_a_791_, v_b_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_795_, lean_object* v_i_796_, lean_object* v_source_797_, lean_object* v_target_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_796_, v_source_797_, v_target_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(uint8_t v_skipIfPropOrEq_804_, lean_object* v_as_805_, size_t v_sz_806_, size_t v_i_807_, lean_object* v_b_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_a_815_; uint8_t v___x_819_; 
v___x_819_ = lean_usize_dec_lt(v_i_807_, v_sz_806_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v_b_808_);
return v___x_820_;
}
else
{
lean_object* v_snd_821_; lean_object* v_fst_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_900_; 
v_snd_821_ = lean_ctor_get(v_b_808_, 1);
v_fst_822_ = lean_ctor_get(v_b_808_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v_b_808_);
if (v_isSharedCheck_900_ == 0)
{
v___x_824_ = v_b_808_;
v_isShared_825_ = v_isSharedCheck_900_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_snd_821_);
lean_inc(v_fst_822_);
lean_dec(v_b_808_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_900_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_array_826_; lean_object* v_start_827_; lean_object* v_stop_828_; uint8_t v___x_829_; 
v_array_826_ = lean_ctor_get(v_snd_821_, 0);
v_start_827_ = lean_ctor_get(v_snd_821_, 1);
v_stop_828_ = lean_ctor_get(v_snd_821_, 2);
v___x_829_ = lean_nat_dec_lt(v_start_827_, v_stop_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_831_; 
if (v_isShared_825_ == 0)
{
v___x_831_ = v___x_824_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_fst_822_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_snd_821_);
v___x_831_ = v_reuseFailAlloc_833_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; 
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
else
{
lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_896_; 
lean_inc(v_stop_828_);
lean_inc(v_start_827_);
lean_inc_ref(v_array_826_);
v_isSharedCheck_896_ = !lean_is_exclusive(v_snd_821_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; lean_object* v_unused_898_; lean_object* v_unused_899_; 
v_unused_897_ = lean_ctor_get(v_snd_821_, 2);
lean_dec(v_unused_897_);
v_unused_898_ = lean_ctor_get(v_snd_821_, 1);
lean_dec(v_unused_898_);
v_unused_899_ = lean_ctor_get(v_snd_821_, 0);
lean_dec(v_unused_899_);
v___x_835_ = v_snd_821_;
v_isShared_836_ = v_isSharedCheck_896_;
goto v_resetjp_834_;
}
else
{
lean_dec(v_snd_821_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_896_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_a_837_; lean_object* v___x_838_; 
v_a_837_ = lean_array_uget_borrowed(v_as_805_, v_i_807_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v_a_837_);
v___x_838_ = lean_infer_type(v_a_837_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref(v___x_838_);
v___x_840_ = lean_array_fget(v_array_826_, v_start_827_);
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_add(v_start_827_, v___x_841_);
lean_dec(v_start_827_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___x_842_);
v___x_844_ = v___x_835_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_array_826_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_stop_828_);
v___x_844_ = v_reuseFailAlloc_887_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
if (v_skipIfPropOrEq_804_ == 0)
{
lean_object* v___x_845_; 
lean_dec(v_a_839_);
lean_inc(v_a_837_);
v___x_845_ = l_Lean_Meta_mkEqHEq(v_a_837_, v___x_840_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
v___x_847_ = lean_array_push(v_fst_822_, v_a_846_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v___x_844_);
lean_ctor_set(v___x_824_, 0, v___x_847_);
v___x_849_ = v___x_824_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
v_a_815_ = v___x_849_;
goto v___jp_814_;
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v___x_844_);
lean_del_object(v___x_824_);
lean_dec(v_fst_822_);
v_a_851_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_845_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_845_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Meta_isProp(v_a_839_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; uint8_t v___x_865_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref(v___x_859_);
v___x_865_ = lean_unbox(v_a_860_);
lean_dec(v_a_860_);
if (v___x_865_ == 0)
{
uint8_t v___x_866_; 
v___x_866_ = lean_expr_eqv(v_a_837_, v___x_840_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
lean_del_object(v___x_824_);
lean_inc(v_a_837_);
v___x_867_ = l_Lean_Meta_mkEqHEq(v_a_837_, v___x_840_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref(v___x_867_);
v___x_869_ = lean_array_push(v_fst_822_, v_a_868_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_844_);
v_a_815_ = v___x_870_;
goto v___jp_814_;
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec_ref(v___x_844_);
lean_dec(v_fst_822_);
v_a_871_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_867_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_867_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_dec(v___x_840_);
goto v___jp_861_;
}
}
else
{
lean_dec(v___x_840_);
goto v___jp_861_;
}
v___jp_861_:
{
lean_object* v___x_863_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v___x_844_);
v___x_863_ = v___x_824_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_fst_822_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_844_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
v_a_815_ = v___x_863_;
goto v___jp_814_;
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec_ref(v___x_844_);
lean_dec(v___x_840_);
lean_del_object(v___x_824_);
lean_dec(v_fst_822_);
v_a_879_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_859_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_859_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_del_object(v___x_835_);
lean_dec(v_stop_828_);
lean_dec(v_start_827_);
lean_dec_ref(v_array_826_);
lean_del_object(v___x_824_);
lean_dec(v_fst_822_);
v_a_888_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_838_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_838_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
}
v___jp_814_:
{
size_t v___x_816_; size_t v___x_817_; 
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_add(v_i_807_, v___x_816_);
v_i_807_ = v___x_817_;
v_b_808_ = v_a_815_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0___boxed(lean_object* v_skipIfPropOrEq_901_, lean_object* v_as_902_, lean_object* v_sz_903_, lean_object* v_i_904_, lean_object* v_b_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_911_; size_t v_sz_boxed_912_; size_t v_i_boxed_913_; lean_object* v_res_914_; 
v_skipIfPropOrEq_boxed_911_ = lean_unbox(v_skipIfPropOrEq_901_);
v_sz_boxed_912_ = lean_unbox_usize(v_sz_903_);
lean_dec(v_sz_903_);
v_i_boxed_913_ = lean_unbox_usize(v_i_904_);
lean_dec(v_i_904_);
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_boxed_911_, v_as_902_, v_sz_boxed_912_, v_i_boxed_913_, v_b_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec_ref(v_as_902_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(lean_object* v_args1_917_, lean_object* v_args2_918_, uint8_t v_skipIfPropOrEq_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_925_; lean_object* v_eqs_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; size_t v_sz_930_; size_t v___x_931_; lean_object* v___x_932_; 
v___x_925_ = lean_unsigned_to_nat(0u);
v_eqs_926_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_927_ = lean_array_get_size(v_args2_918_);
v___x_928_ = l_Array_toSubarray___redArg(v_args2_918_, v___x_925_, v___x_927_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_eqs_926_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v_sz_930_ = lean_array_size(v_args1_917_);
v___x_931_ = ((size_t)0ULL);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkEqs_spec__0(v_skipIfPropOrEq_919_, v_args1_917_, v_sz_930_, v___x_931_, v___x_929_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_941_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_941_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_fst_937_; lean_object* v___x_939_; 
v_fst_937_ = lean_ctor_get(v_a_933_, 0);
lean_inc(v_fst_937_);
lean_dec(v_a_933_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v_fst_937_);
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_fst_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_932_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_932_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___boxed(lean_object* v_args1_950_, lean_object* v_args2_951_, lean_object* v_skipIfPropOrEq_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
uint8_t v_skipIfPropOrEq_boxed_958_; lean_object* v_res_959_; 
v_skipIfPropOrEq_boxed_958_ = lean_unbox(v_skipIfPropOrEq_952_);
v_res_959_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_950_, v_args2_951_, v_skipIfPropOrEq_boxed_958_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec_ref(v_args1_950_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(lean_object* v_k_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
v___x_967_ = lean_apply_6(v_k_960_, v_b_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, lean_box(0));
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed(lean_object* v_k_968_, lean_object* v_b_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0(v_k_968_, v_b_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(lean_object* v_name_976_, uint8_t v_bi_977_, lean_object* v_type_978_, lean_object* v_k_979_, uint8_t v_kind_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___f_986_; lean_object* v___x_987_; 
v___f_986_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_986_, 0, v_k_979_);
v___x_987_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_976_, v_bi_977_, v_type_978_, v___f_986_, v_kind_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
v_a_996_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_987_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_987_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg___boxed(lean_object* v_name_1004_, lean_object* v_bi_1005_, lean_object* v_type_1006_, lean_object* v_k_1007_, lean_object* v_kind_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
uint8_t v_bi_boxed_1014_; uint8_t v_kind_boxed_1015_; lean_object* v_res_1016_; 
v_bi_boxed_1014_ = lean_unbox(v_bi_1005_);
v_kind_boxed_1015_ = lean_unbox(v_kind_1008_);
v_res_1016_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1004_, v_bi_boxed_1014_, v_type_1006_, v_k_1007_, v_kind_boxed_1015_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(lean_object* v_00_u03b1_1017_, lean_object* v_name_1018_, uint8_t v_bi_1019_, lean_object* v_type_1020_, lean_object* v_k_1021_, uint8_t v_kind_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_name_1018_, v_bi_1019_, v_type_1020_, v_k_1021_, v_kind_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_name_1030_, lean_object* v_bi_1031_, lean_object* v_type_1032_, lean_object* v_k_1033_, lean_object* v_kind_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v_bi_boxed_1040_; uint8_t v_kind_boxed_1041_; lean_object* v_res_1042_; 
v_bi_boxed_1040_ = lean_unbox(v_bi_1031_);
v_kind_boxed_1041_ = lean_unbox(v_kind_1034_);
v_res_1042_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0(v_00_u03b1_1029_, v_name_1030_, v_bi_boxed_1040_, v_type_1032_, v_k_1033_, v_kind_boxed_1041_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(lean_object* v_msgData_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v___x_1049_; lean_object* v_env_1050_; lean_object* v___x_1051_; lean_object* v_mctx_1052_; lean_object* v_lctx_1053_; lean_object* v_options_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1049_ = lean_st_ref_get(v___y_1047_);
v_env_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc_ref(v_env_1050_);
lean_dec(v___x_1049_);
v___x_1051_ = lean_st_ref_get(v___y_1045_);
v_mctx_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc_ref(v_mctx_1052_);
lean_dec(v___x_1051_);
v_lctx_1053_ = lean_ctor_get(v___y_1044_, 2);
v_options_1054_ = lean_ctor_get(v___y_1046_, 2);
lean_inc_ref(v_options_1054_);
lean_inc_ref(v_lctx_1053_);
v___x_1055_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1055_, 0, v_env_1050_);
lean_ctor_set(v___x_1055_, 1, v_mctx_1052_);
lean_ctor_set(v___x_1055_, 2, v_lctx_1053_);
lean_ctor_set(v___x_1055_, 3, v_options_1054_);
v___x_1056_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v_msgData_1043_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1___boxed(lean_object* v_msgData_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msgData_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(lean_object* v_msg_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_ref_1071_; lean_object* v___x_1072_; lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1081_; 
v_ref_1071_ = lean_ctor_get(v___y_1068_, 5);
v___x_1072_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_inc(v_ref_1071_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_ref_1071_);
lean_ctor_set(v___x_1077_, 1, v_a_1073_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 1);
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg___boxed(lean_object* v_msg_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_1089_, lean_object* v_body_1090_, lean_object* v_args2_1091_, lean_object* v_args2New_1092_, lean_object* v_ctorVal_1093_, lean_object* v_useEq_1094_, lean_object* v_args1_1095_, lean_object* v_resultType_1096_, lean_object* v_k_1097_, lean_object* v_arg2_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v_useEq_boxed_1104_; lean_object* v_res_1105_; 
v_useEq_boxed_1104_ = lean_unbox(v_useEq_1094_);
v_res_1105_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(v_i_1089_, v_body_1090_, v_args2_1091_, v_args2New_1092_, v_ctorVal_1093_, v_useEq_boxed_1104_, v_args1_1095_, v_resultType_1096_, v_k_1097_, v_arg2_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec_ref(v_body_1090_);
lean_dec(v_i_1089_);
return v_res_1105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__0));
v___x_1108_ = l_Lean_stringToMessageData(v___x_1107_);
return v___x_1108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__2));
v___x_1111_ = l_Lean_stringToMessageData(v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(lean_object* v_ctorVal_1112_, uint8_t v_useEq_1113_, lean_object* v_args1_1114_, lean_object* v_resultType_1115_, lean_object* v_k_1116_, lean_object* v_i_1117_, lean_object* v_type_1118_, lean_object* v_args2_1119_, lean_object* v_args2New_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_array_get_size(v_args1_1114_);
v___x_1127_ = lean_nat_dec_lt(v_i_1117_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v_type_1118_);
lean_dec(v_i_1117_);
lean_dec_ref(v_resultType_1115_);
lean_dec_ref(v_args1_1114_);
lean_dec_ref(v_ctorVal_1112_);
lean_inc(v_a_1124_);
lean_inc_ref(v_a_1123_);
lean_inc(v_a_1122_);
v___x_1128_ = lean_apply_7(v_k_1116_, v_args2_1119_, v_args2New_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, lean_box(0));
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; 
lean_inc(v_a_1124_);
lean_inc_ref(v_a_1123_);
lean_inc(v_a_1122_);
lean_inc_ref(v_a_1121_);
v___x_1129_ = lean_whnf(v_type_1118_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref(v___x_1129_);
if (lean_obj_tag(v_a_1130_) == 7)
{
lean_object* v_binderName_1131_; lean_object* v_binderType_1132_; lean_object* v_body_1133_; lean_object* v_lctx_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v_binderName_1131_ = lean_ctor_get(v_a_1130_, 0);
lean_inc(v_binderName_1131_);
v_binderType_1132_ = lean_ctor_get(v_a_1130_, 1);
lean_inc_ref(v_binderType_1132_);
v_body_1133_ = lean_ctor_get(v_a_1130_, 2);
lean_inc_ref(v_body_1133_);
lean_dec_ref(v_a_1130_);
v_lctx_1134_ = lean_ctor_get(v_a_1121_, 2);
v___x_1135_ = lean_array_fget_borrowed(v_args1_1114_, v_i_1117_);
lean_inc(v___x_1135_);
lean_inc_ref(v_lctx_1134_);
v___x_1136_ = l_Lean_Meta_occursOrInType(v_lctx_1134_, v___x_1135_, v_resultType_1115_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___f_1138_; uint8_t v___y_1140_; 
v___x_1137_ = lean_box(v_useEq_1113_);
v___f_1138_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0___boxed), 15, 9);
lean_closure_set(v___f_1138_, 0, v_i_1117_);
lean_closure_set(v___f_1138_, 1, v_body_1133_);
lean_closure_set(v___f_1138_, 2, v_args2_1119_);
lean_closure_set(v___f_1138_, 3, v_args2New_1120_);
lean_closure_set(v___f_1138_, 4, v_ctorVal_1112_);
lean_closure_set(v___f_1138_, 5, v___x_1137_);
lean_closure_set(v___f_1138_, 6, v_args1_1114_);
lean_closure_set(v___f_1138_, 7, v_resultType_1115_);
lean_closure_set(v___f_1138_, 8, v_k_1116_);
if (v_useEq_1113_ == 0)
{
uint8_t v___x_1143_; 
v___x_1143_ = 1;
v___y_1140_ = v___x_1143_;
goto v___jp_1139_;
}
else
{
uint8_t v___x_1144_; 
v___x_1144_ = 0;
v___y_1140_ = v___x_1144_;
goto v___jp_1139_;
}
v___jp_1139_:
{
uint8_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = 0;
v___x_1142_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_1131_, v___y_1140_, v_binderType_1132_, v___f_1138_, v___x_1141_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec_ref(v_a_1121_);
return v___x_1142_;
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref(v_binderType_1132_);
lean_dec(v_binderName_1131_);
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = lean_nat_add(v_i_1117_, v___x_1145_);
lean_dec(v_i_1117_);
v___x_1147_ = lean_expr_instantiate1(v_body_1133_, v___x_1135_);
lean_dec_ref(v_body_1133_);
lean_inc(v___x_1135_);
v___x_1148_ = lean_array_push(v_args2_1119_, v___x_1135_);
v_i_1117_ = v___x_1146_;
v_type_1118_ = v___x_1147_;
v_args2_1119_ = v___x_1148_;
goto _start;
}
}
else
{
lean_object* v_toConstantVal_1150_; lean_object* v_name_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec(v_a_1130_);
lean_dec_ref(v_args2New_1120_);
lean_dec_ref(v_args2_1119_);
lean_dec(v_i_1117_);
lean_dec_ref(v_k_1116_);
lean_dec_ref(v_resultType_1115_);
lean_dec_ref(v_args1_1114_);
v_toConstantVal_1150_ = lean_ctor_get(v_ctorVal_1112_, 0);
lean_inc_ref(v_toConstantVal_1150_);
lean_dec_ref(v_ctorVal_1112_);
v_name_1151_ = lean_ctor_get(v_toConstantVal_1150_, 0);
lean_inc(v_name_1151_);
lean_dec_ref(v_toConstantVal_1150_);
v___x_1152_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_1153_ = l_Lean_MessageData_ofName(v_name_1151_);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1156_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec_ref(v_a_1121_);
return v___x_1157_;
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v_a_1121_);
lean_dec_ref(v_args2New_1120_);
lean_dec_ref(v_args2_1119_);
lean_dec(v_i_1117_);
lean_dec_ref(v_k_1116_);
lean_dec_ref(v_resultType_1115_);
lean_dec_ref(v_args1_1114_);
lean_dec_ref(v_ctorVal_1112_);
v_a_1158_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1129_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1129_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___lam__0(lean_object* v_i_1166_, lean_object* v_body_1167_, lean_object* v_args2_1168_, lean_object* v_args2New_1169_, lean_object* v_ctorVal_1170_, uint8_t v_useEq_1171_, lean_object* v_args1_1172_, lean_object* v_resultType_1173_, lean_object* v_k_1174_, lean_object* v_arg2_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1181_ = lean_unsigned_to_nat(1u);
v___x_1182_ = lean_nat_add(v_i_1166_, v___x_1181_);
v___x_1183_ = lean_expr_instantiate1(v_body_1167_, v_arg2_1175_);
lean_inc_ref(v_arg2_1175_);
v___x_1184_ = lean_array_push(v_args2_1168_, v_arg2_1175_);
v___x_1185_ = lean_array_push(v_args2New_1169_, v_arg2_1175_);
lean_inc_ref(v___y_1176_);
v___x_1186_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1170_, v_useEq_1171_, v_args1_1172_, v_resultType_1173_, v_k_1174_, v___x_1182_, v___x_1183_, v___x_1184_, v___x_1185_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed(lean_object* v_ctorVal_1187_, lean_object* v_useEq_1188_, lean_object* v_args1_1189_, lean_object* v_resultType_1190_, lean_object* v_k_1191_, lean_object* v_i_1192_, lean_object* v_type_1193_, lean_object* v_args2_1194_, lean_object* v_args2New_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
uint8_t v_useEq_boxed_1201_; lean_object* v_res_1202_; 
v_useEq_boxed_1201_ = lean_unbox(v_useEq_1188_);
v_res_1202_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1187_, v_useEq_boxed_1201_, v_args1_1189_, v_resultType_1190_, v_k_1191_, v_i_1192_, v_type_1193_, v_args2_1194_, v_args2New_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(lean_object* v_00_u03b1_1203_, lean_object* v_msg_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___boxed(lean_object* v_00_u03b1_1211_, lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1(v_00_u03b1_1211_, v_msg_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter___redArg(lean_object* v_____x_1219_, lean_object* v_h__1_1220_, lean_object* v_h__2_1221_){
_start:
{
if (lean_obj_tag(v_____x_1219_) == 7)
{
lean_object* v_binderName_1222_; lean_object* v_binderType_1223_; lean_object* v_body_1224_; uint8_t v_binderInfo_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec(v_h__2_1221_);
v_binderName_1222_ = lean_ctor_get(v_____x_1219_, 0);
lean_inc(v_binderName_1222_);
v_binderType_1223_ = lean_ctor_get(v_____x_1219_, 1);
lean_inc_ref(v_binderType_1223_);
v_body_1224_ = lean_ctor_get(v_____x_1219_, 2);
lean_inc_ref(v_body_1224_);
v_binderInfo_1225_ = lean_ctor_get_uint8(v_____x_1219_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1219_);
v___x_1226_ = lean_box(v_binderInfo_1225_);
v___x_1227_ = lean_apply_4(v_h__1_1220_, v_binderName_1222_, v_binderType_1223_, v_body_1224_, v___x_1226_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; 
lean_dec(v_h__1_1220_);
v___x_1228_ = lean_apply_2(v_h__2_1221_, v_____x_1219_, lean_box(0));
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_match__1_splitter(lean_object* v_motive_1229_, lean_object* v_____x_1230_, lean_object* v_h__1_1231_, lean_object* v_h__2_1232_){
_start:
{
if (lean_obj_tag(v_____x_1230_) == 7)
{
lean_object* v_binderName_1233_; lean_object* v_binderType_1234_; lean_object* v_body_1235_; uint8_t v_binderInfo_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_h__2_1232_);
v_binderName_1233_ = lean_ctor_get(v_____x_1230_, 0);
lean_inc(v_binderName_1233_);
v_binderType_1234_ = lean_ctor_get(v_____x_1230_, 1);
lean_inc_ref(v_binderType_1234_);
v_body_1235_ = lean_ctor_get(v_____x_1230_, 2);
lean_inc_ref(v_body_1235_);
v_binderInfo_1236_ = lean_ctor_get_uint8(v_____x_1230_, sizeof(void*)*3 + 8);
lean_dec_ref(v_____x_1230_);
v___x_1237_ = lean_box(v_binderInfo_1236_);
v___x_1238_ = lean_apply_4(v_h__1_1231_, v_binderName_1233_, v_binderType_1234_, v_body_1235_, v___x_1237_);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; 
lean_dec(v_h__1_1231_);
v___x_1239_ = lean_apply_2(v_h__2_1232_, v_____x_1230_, lean_box(0));
return v___x_1239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(lean_object* v_k_1240_, lean_object* v_b_1241_, lean_object* v_c_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
v___x_1248_ = lean_apply_7(v_k_1240_, v_b_1241_, v_c_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, lean_box(0));
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed(lean_object* v_k_1249_, lean_object* v_b_1250_, lean_object* v_c_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0(v_k_1249_, v_b_1250_, v_c_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(lean_object* v_type_1258_, lean_object* v_k_1259_, uint8_t v_cleanupAnnotations_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___f_1266_; uint8_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___f_1266_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1266_, 0, v_k_1259_);
v___x_1267_ = 0;
v___x_1268_ = lean_box(0);
v___x_1269_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1267_, v___x_1268_, v_type_1258_, v___f_1266_, v_cleanupAnnotations_1260_, v___x_1267_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
v_a_1278_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1269_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1269_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___boxed(lean_object* v_type_1286_, lean_object* v_k_1287_, lean_object* v_cleanupAnnotations_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1294_; lean_object* v_res_1295_; 
v_cleanupAnnotations_boxed_1294_ = lean_unbox(v_cleanupAnnotations_1288_);
v_res_1295_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1286_, v_k_1287_, v_cleanupAnnotations_boxed_1294_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(lean_object* v_00_u03b1_1296_, lean_object* v_type_1297_, lean_object* v_k_1298_, uint8_t v_cleanupAnnotations_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1297_, v_k_1298_, v_cleanupAnnotations_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_type_1307_, lean_object* v_k_1308_, lean_object* v_cleanupAnnotations_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1315_; lean_object* v_res_1316_; 
v_cleanupAnnotations_boxed_1315_ = lean_unbox(v_cleanupAnnotations_1309_);
v_res_1316_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2(v_00_u03b1_1306_, v_type_1307_, v_k_1308_, v_cleanupAnnotations_boxed_1315_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(lean_object* v_type_1317_, lean_object* v_maxFVars_x3f_1318_, lean_object* v_k_1319_, uint8_t v_cleanupAnnotations_1320_, uint8_t v_whnfType_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___f_1327_; lean_object* v___x_1328_; 
v___f_1327_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1327_, 0, v_k_1319_);
v___x_1328_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1317_, v_maxFVars_x3f_1318_, v___f_1327_, v_cleanupAnnotations_1320_, v_whnfType_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
v_a_1337_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1328_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1328_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg___boxed(lean_object* v_type_1345_, lean_object* v_maxFVars_x3f_1346_, lean_object* v_k_1347_, lean_object* v_cleanupAnnotations_1348_, lean_object* v_whnfType_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1355_; uint8_t v_whnfType_boxed_1356_; lean_object* v_res_1357_; 
v_cleanupAnnotations_boxed_1355_ = lean_unbox(v_cleanupAnnotations_1348_);
v_whnfType_boxed_1356_ = lean_unbox(v_whnfType_1349_);
v_res_1357_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1345_, v_maxFVars_x3f_1346_, v_k_1347_, v_cleanupAnnotations_boxed_1355_, v_whnfType_boxed_1356_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(lean_object* v_00_u03b1_1358_, lean_object* v_type_1359_, lean_object* v_maxFVars_x3f_1360_, lean_object* v_k_1361_, uint8_t v_cleanupAnnotations_1362_, uint8_t v_whnfType_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_type_1359_, v_maxFVars_x3f_1360_, v_k_1361_, v_cleanupAnnotations_1362_, v_whnfType_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___boxed(lean_object* v_00_u03b1_1370_, lean_object* v_type_1371_, lean_object* v_maxFVars_x3f_1372_, lean_object* v_k_1373_, lean_object* v_cleanupAnnotations_1374_, lean_object* v_whnfType_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1381_; uint8_t v_whnfType_boxed_1382_; lean_object* v_res_1383_; 
v_cleanupAnnotations_boxed_1381_ = lean_unbox(v_cleanupAnnotations_1374_);
v_whnfType_boxed_1382_ = lean_unbox(v_whnfType_1375_);
v_res_1383_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3(v_00_u03b1_1370_, v_type_1371_, v_maxFVars_x3f_1372_, v_k_1373_, v_cleanupAnnotations_boxed_1381_, v_whnfType_boxed_1382_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(lean_object* v_name_1384_, lean_object* v_us_1385_, lean_object* v_params_1386_, lean_object* v_args1_1387_, uint8_t v_useEq_1388_, lean_object* v_args2_1389_, lean_object* v_args2New_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1396_ = l_Lean_mkConst(v_name_1384_, v_us_1385_);
v___x_1397_ = l_Lean_mkAppN(v___x_1396_, v_params_1386_);
lean_inc_ref(v___x_1397_);
v___x_1398_ = l_Lean_mkAppN(v___x_1397_, v_args1_1387_);
v___x_1399_ = l_Lean_mkAppN(v___x_1397_, v_args2_1389_);
v___x_1400_ = l_Lean_Meta_mkEq(v___x_1398_, v___x_1399_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; uint8_t v___x_1402_; lean_object* v_result_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___x_1449_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = 1;
v___x_1449_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_1387_, v_args2_1389_, v___x_1402_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1481_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1481_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1481_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; 
v___x_1454_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_1450_);
if (lean_obj_tag(v___x_1454_) == 1)
{
lean_del_object(v___x_1452_);
if (v_useEq_1388_ == 0)
{
lean_object* v_val_1455_; lean_object* v___x_1456_; 
v_val_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_val_1455_);
lean_dec_ref(v___x_1454_);
v___x_1456_ = l_Lean_mkArrow(v_a_1401_, v_val_1455_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1456_);
v_result_1404_ = v_a_1457_;
v___y_1405_ = v___y_1391_;
v___y_1406_ = v___y_1392_;
v___y_1407_ = v___y_1393_;
v___y_1408_ = v___y_1394_;
goto v___jp_1403_;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_a_1458_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1456_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1456_);
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
lean_object* v_val_1466_; lean_object* v___x_1467_; 
v_val_1466_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_val_1466_);
lean_dec_ref(v___x_1454_);
v___x_1467_ = l_Lean_Meta_mkEq(v_a_1401_, v_val_1466_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref(v___x_1467_);
v_result_1404_ = v_a_1468_;
v___y_1405_ = v___y_1391_;
v___y_1406_ = v___y_1392_;
v___y_1407_ = v___y_1393_;
v___y_1408_ = v___y_1394_;
goto v___jp_1403_;
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_a_1469_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1467_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_dec(v___x_1454_);
lean_dec(v_a_1401_);
v___x_1477_ = lean_box(0);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1477_);
v___x_1479_ = v___x_1452_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
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
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_a_1401_);
v_a_1482_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1449_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1449_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
v___jp_1403_:
{
uint8_t v___x_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = 0;
v___x_1410_ = 1;
v___x_1411_ = l_Lean_Meta_mkForallFVars(v_args2New_1390_, v_result_1404_, v___x_1409_, v___x_1402_, v___x_1402_, v___x_1410_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref(v___x_1411_);
v___x_1413_ = l_Lean_Meta_mkForallFVars(v_args1_1387_, v_a_1412_, v___x_1409_, v___x_1402_, v___x_1402_, v___x_1410_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref(v___x_1413_);
v___x_1415_ = l_Lean_Meta_mkForallFVars(v_params_1386_, v_a_1414_, v___x_1409_, v___x_1402_, v___x_1402_, v___x_1410_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_a_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
v_a_1425_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1415_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1415_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
v_a_1433_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1413_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1413_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_a_1441_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1411_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1411_);
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
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec_ref(v_args2_1389_);
v_a_1490_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1400_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1400_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed(lean_object* v_name_1498_, lean_object* v_us_1499_, lean_object* v_params_1500_, lean_object* v_args1_1501_, lean_object* v_useEq_1502_, lean_object* v_args2_1503_, lean_object* v_args2New_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v_useEq_boxed_1510_; lean_object* v_res_1511_; 
v_useEq_boxed_1510_ = lean_unbox(v_useEq_1502_);
v_res_1511_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0(v_name_1498_, v_us_1499_, v_params_1500_, v_args1_1501_, v_useEq_boxed_1510_, v_args2_1503_, v_args2New_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec_ref(v_args2New_1504_);
lean_dec_ref(v_args1_1501_);
lean_dec_ref(v_params_1500_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(size_t v_sz_1512_, size_t v_i_1513_, lean_object* v_bs_1514_){
_start:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_usize_dec_lt(v_i_1513_, v_sz_1512_);
if (v___x_1515_ == 0)
{
return v_bs_1514_;
}
else
{
lean_object* v_v_1516_; lean_object* v___x_1517_; lean_object* v_bs_x27_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; size_t v___x_1523_; size_t v___x_1524_; lean_object* v___x_1525_; 
v_v_1516_ = lean_array_uget(v_bs_1514_, v_i_1513_);
v___x_1517_ = lean_unsigned_to_nat(0u);
v_bs_x27_1518_ = lean_array_uset(v_bs_1514_, v_i_1513_, v___x_1517_);
v___x_1519_ = l_Lean_Expr_fvarId_x21(v_v_1516_);
lean_dec(v_v_1516_);
v___x_1520_ = 1;
v___x_1521_ = lean_box(v___x_1520_);
v___x_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1519_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = ((size_t)1ULL);
v___x_1524_ = lean_usize_add(v_i_1513_, v___x_1523_);
v___x_1525_ = lean_array_uset(v_bs_x27_1518_, v_i_1513_, v___x_1522_);
v_i_1513_ = v___x_1524_;
v_bs_1514_ = v___x_1525_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1___boxed(lean_object* v_sz_1527_, lean_object* v_i_1528_, lean_object* v_bs_1529_){
_start:
{
size_t v_sz_boxed_1530_; size_t v_i_boxed_1531_; lean_object* v_res_1532_; 
v_sz_boxed_1530_ = lean_unbox_usize(v_sz_1527_);
lean_dec(v_sz_1527_);
v_i_boxed_1531_ = lean_unbox_usize(v_i_1528_);
lean_dec(v_i_1528_);
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_boxed_1530_, v_i_boxed_1531_, v_bs_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(lean_object* v_bs_1533_, lean_object* v_k_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; 
v___x_1540_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1533_, v_k_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_a_1549_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1540_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1540_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_bs_1557_, lean_object* v_k_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1557_, v_k_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec_ref(v_bs_1557_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(lean_object* v_bs_1565_, lean_object* v_k_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
size_t v_sz_1572_; size_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v_sz_1572_ = lean_array_size(v_bs_1565_);
v___x_1573_ = ((size_t)0ULL);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__1(v_sz_1572_, v___x_1573_, v_bs_1565_);
v___x_1575_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v___x_1574_, v_k_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec_ref(v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg___boxed(lean_object* v_bs_1576_, lean_object* v_k_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1576_, v_k_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(lean_object* v_name_1584_, lean_object* v_us_1585_, lean_object* v_params_1586_, uint8_t v_useEq_1587_, lean_object* v_ctorVal_1588_, lean_object* v_type_1589_, lean_object* v_args1_1590_, lean_object* v_resultType_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v___f_1598_; 
v___x_1597_ = lean_box(v_useEq_1587_);
lean_inc_ref(v_args1_1590_);
lean_inc_ref(v_params_1586_);
v___f_1598_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1598_, 0, v_name_1584_);
lean_closure_set(v___f_1598_, 1, v_us_1585_);
lean_closure_set(v___f_1598_, 2, v_params_1586_);
lean_closure_set(v___f_1598_, 3, v_args1_1590_);
lean_closure_set(v___f_1598_, 4, v___x_1597_);
if (v_useEq_1587_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1599_ = l_Array_append___redArg(v_params_1586_, v_args1_1590_);
v___x_1600_ = lean_unsigned_to_nat(0u);
v___x_1601_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_1602_ = lean_box(v_useEq_1587_);
v___x_1603_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___boxed), 14, 9);
lean_closure_set(v___x_1603_, 0, v_ctorVal_1588_);
lean_closure_set(v___x_1603_, 1, v___x_1602_);
lean_closure_set(v___x_1603_, 2, v_args1_1590_);
lean_closure_set(v___x_1603_, 3, v_resultType_1591_);
lean_closure_set(v___x_1603_, 4, v___f_1598_);
lean_closure_set(v___x_1603_, 5, v___x_1600_);
lean_closure_set(v___x_1603_, 6, v_type_1589_);
lean_closure_set(v___x_1603_, 7, v___x_1601_);
lean_closure_set(v___x_1603_, 8, v___x_1601_);
v___x_1604_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v___x_1599_, v___x_1603_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec_ref(v_params_1586_);
v___x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
lean_inc_ref(v___y_1592_);
v___x_1607_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2(v_ctorVal_1588_, v_useEq_1587_, v_args1_1590_, v_resultType_1591_, v___f_1598_, v___x_1605_, v_type_1589_, v___x_1606_, v___x_1606_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed(lean_object* v_name_1608_, lean_object* v_us_1609_, lean_object* v_params_1610_, lean_object* v_useEq_1611_, lean_object* v_ctorVal_1612_, lean_object* v_type_1613_, lean_object* v_args1_1614_, lean_object* v_resultType_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
uint8_t v_useEq_boxed_1621_; lean_object* v_res_1622_; 
v_useEq_boxed_1621_ = lean_unbox(v_useEq_1611_);
v_res_1622_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1(v_name_1608_, v_us_1609_, v_params_1610_, v_useEq_boxed_1621_, v_ctorVal_1612_, v_type_1613_, v_args1_1614_, v_resultType_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(lean_object* v_name_1623_, lean_object* v_us_1624_, uint8_t v_useEq_1625_, lean_object* v_ctorVal_1626_, lean_object* v_params_1627_, lean_object* v_type_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; lean_object* v___f_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
v___x_1634_ = lean_box(v_useEq_1625_);
lean_inc_ref(v_type_1628_);
v___f_1635_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__1___boxed), 13, 6);
lean_closure_set(v___f_1635_, 0, v_name_1623_);
lean_closure_set(v___f_1635_, 1, v_us_1624_);
lean_closure_set(v___f_1635_, 2, v_params_1627_);
lean_closure_set(v___f_1635_, 3, v___x_1634_);
lean_closure_set(v___f_1635_, 4, v_ctorVal_1626_);
lean_closure_set(v___f_1635_, 5, v_type_1628_);
v___x_1636_ = 0;
v___x_1637_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_type_1628_, v___f_1635_, v___x_1636_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed(lean_object* v_name_1638_, lean_object* v_us_1639_, lean_object* v_useEq_1640_, lean_object* v_ctorVal_1641_, lean_object* v_params_1642_, lean_object* v_type_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v_useEq_boxed_1649_; lean_object* v_res_1650_; 
v_useEq_boxed_1649_ = lean_unbox(v_useEq_1640_);
v_res_1650_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2(v_name_1638_, v_us_1639_, v_useEq_boxed_1649_, v_ctorVal_1641_, v_params_1642_, v_type_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
if (lean_obj_tag(v_a_1651_) == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = l_List_reverse___redArg(v_a_1652_);
return v___x_1653_;
}
else
{
lean_object* v_head_1654_; lean_object* v_tail_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1664_; 
v_head_1654_ = lean_ctor_get(v_a_1651_, 0);
v_tail_1655_ = lean_ctor_get(v_a_1651_, 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_a_1651_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1657_ = v_a_1651_;
v_isShared_1658_ = v_isSharedCheck_1664_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_tail_1655_);
lean_inc(v_head_1654_);
lean_dec(v_a_1651_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1664_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = l_Lean_mkLevelParam(v_head_1654_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v_a_1652_);
lean_ctor_set(v___x_1657_, 0, v___x_1659_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_a_1652_);
v___x_1661_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
v_a_1651_ = v_tail_1655_;
v_a_1652_ = v___x_1661_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(lean_object* v_ctorVal_1665_, uint8_t v_useEq_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_toConstantVal_1672_; lean_object* v_numParams_1673_; lean_object* v_name_1674_; lean_object* v_levelParams_1675_; lean_object* v_type_1676_; lean_object* v___x_1677_; 
v_toConstantVal_1672_ = lean_ctor_get(v_ctorVal_1665_, 0);
v_numParams_1673_ = lean_ctor_get(v_ctorVal_1665_, 3);
lean_inc(v_numParams_1673_);
v_name_1674_ = lean_ctor_get(v_toConstantVal_1672_, 0);
lean_inc(v_name_1674_);
v_levelParams_1675_ = lean_ctor_get(v_toConstantVal_1672_, 1);
v_type_1676_ = lean_ctor_get(v_toConstantVal_1672_, 2);
lean_inc_ref(v_type_1676_);
v___x_1677_ = l_Lean_Meta_elimOptParam(v_type_1676_, v_a_1669_, v_a_1670_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1679_; lean_object* v_us_1680_; lean_object* v___x_1681_; lean_object* v___f_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref(v___x_1677_);
v___x_1679_ = lean_box(0);
lean_inc(v_levelParams_1675_);
v_us_1680_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_1675_, v___x_1679_);
v___x_1681_ = lean_box(v_useEq_1666_);
v___f_1682_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___lam__2___boxed), 11, 4);
lean_closure_set(v___f_1682_, 0, v_name_1674_);
lean_closure_set(v___f_1682_, 1, v_us_1680_);
lean_closure_set(v___f_1682_, 2, v___x_1681_);
lean_closure_set(v___f_1682_, 3, v_ctorVal_1665_);
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_numParams_1673_);
v___x_1684_ = 0;
v___x_1685_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__3___redArg(v_a_1678_, v___x_1683_, v___f_1682_, v___x_1684_, v___x_1684_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
return v___x_1685_;
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_name_1674_);
lean_dec(v_numParams_1673_);
lean_dec_ref(v_ctorVal_1665_);
v_a_1686_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1677_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1677_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f___boxed(lean_object* v_ctorVal_1694_, lean_object* v_useEq_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
uint8_t v_useEq_boxed_1701_; lean_object* v_res_1702_; 
v_useEq_boxed_1701_ = lean_unbox(v_useEq_1695_);
v_res_1702_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1694_, v_useEq_boxed_1701_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1703_, lean_object* v_bs_1704_, lean_object* v_k_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___redArg(v_bs_1704_, v_k_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1712_, lean_object* v_bs_1713_, lean_object* v_k_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1_spec__2(v_00_u03b1_1712_, v_bs_1713_, v_k_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec_ref(v_bs_1713_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(lean_object* v_00_u03b1_1721_, lean_object* v_bs_1722_, lean_object* v_k_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_bs_1722_, v_k_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___boxed(lean_object* v_00_u03b1_1730_, lean_object* v_bs_1731_, lean_object* v_k_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1(v_00_u03b1_1730_, v_bs_1731_, v_k_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(lean_object* v_ctorVal_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
uint8_t v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = 0;
v___x_1746_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_1739_, v___x_1745_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f___boxed(lean_object* v_ctorVal_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
return v_res_1753_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__0));
v___x_1756_ = l_Lean_stringToMessageData(v___x_1755_);
return v___x_1756_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__2));
v___x_1759_ = l_Lean_stringToMessageData(v___x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(lean_object* v_ctorName_1760_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1761_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__1);
v___x_1762_ = l_Lean_MessageData_ofName(v_ctorName_1760_);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader___closed__3);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(lean_object* v_ctorName_1766_, lean_object* v_mvarId_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1773_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_ctorName_1766_);
v___x_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_mvarId_1767_);
v___x_1775_ = l_Lean_indentD(v___x_1774_);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1773_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_1776_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg___boxed(lean_object* v_ctorName_1778_, lean_object* v_mvarId_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1778_, v_mvarId_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(lean_object* v_00_u03b1_1786_, lean_object* v_ctorName_1787_, lean_object* v_mvarId_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1787_, v_mvarId_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___boxed(lean_object* v_00_u03b1_1795_, lean_object* v_ctorName_1796_, lean_object* v_mvarId_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure(v_00_u03b1_1795_, v_ctorName_1796_, v_mvarId_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(lean_object* v_ctorName_1804_, lean_object* v_as_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
if (lean_obj_tag(v_as_1805_) == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_dec(v_ctorName_1804_);
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
else
{
lean_object* v_head_1813_; lean_object* v_tail_1814_; lean_object* v___x_1815_; 
v_head_1813_ = lean_ctor_get(v_as_1805_, 0);
lean_inc(v_head_1813_);
v_tail_1814_ = lean_ctor_get(v_as_1805_, 1);
lean_inc(v_tail_1814_);
lean_dec_ref(v_as_1805_);
lean_inc(v_head_1813_);
v___x_1815_ = l_Lean_MVarId_assumptionCore(v_head_1813_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; uint8_t v___x_1817_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref(v___x_1815_);
v___x_1817_ = lean_unbox(v_a_1816_);
lean_dec(v_a_1816_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; 
lean_dec(v_tail_1814_);
v___x_1818_ = l___private_Lean_Meta_Injective_0__Lean_Meta_throwInjectiveTheoremFailure___redArg(v_ctorName_1804_, v_head_1813_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
return v___x_1818_;
}
else
{
lean_dec(v_head_1813_);
v_as_1805_ = v_tail_1814_;
goto _start;
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_tail_1814_);
lean_dec(v_head_1813_);
lean_dec(v_ctorName_1804_);
v_a_1820_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1815_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1815_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0___boxed(lean_object* v_ctorName_1828_, lean_object* v_as_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1828_, v_as_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(lean_object* v_mvarId_1836_, lean_object* v_ctorName_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_MVarId_splitAndCore(v_mvarId_1836_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v___x_1845_ = l_List_forM___at___00__private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption_spec__0(v_ctorName_1837_, v_a_1844_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
return v___x_1845_;
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v_ctorName_1837_);
v_a_1846_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1843_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1843_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption___boxed(lean_object* v_mvarId_1854_, lean_object* v_ctorName_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_1854_, v_ctorName_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(lean_object* v_msg_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___f_1869_; lean_object* v___x_559__overap_1870_; lean_object* v___x_1871_; 
v___f_1869_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___closed__0));
v___x_559__overap_1870_ = lean_panic_fn(v___f_1869_, v_msg_1863_);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
v___x_1871_ = lean_apply_5(v___x_559__overap_1870_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, lean_box(0));
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0___boxed(lean_object* v_msg_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v_msg_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(lean_object* v_cls_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_options_1885_; uint8_t v_hasTrace_1886_; 
v_options_1885_ = lean_ctor_get(v___y_1883_, 2);
v_hasTrace_1886_ = lean_ctor_get_uint8(v_options_1885_, sizeof(void*)*1);
if (v_hasTrace_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec(v_cls_1882_);
v___x_1887_ = lean_box(v_hasTrace_1886_);
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
return v___x_1888_;
}
else
{
lean_object* v_inheritedTraceOptions_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_inheritedTraceOptions_1889_ = lean_ctor_get(v___y_1883_, 13);
v___x_1890_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg___closed__1));
v___x_1891_ = l_Lean_Name_append(v___x_1890_, v_cls_1882_);
v___x_1892_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1889_, v_options_1885_, v___x_1891_);
lean_dec(v___x_1891_);
v___x_1893_ = lean_box(v___x_1892_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg___boxed(lean_object* v_cls_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_1895_, v___y_1896_);
lean_dec_ref(v___y_1896_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(lean_object* v_cls_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_1899_, v___y_1902_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___boxed(lean_object* v_cls_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1(v_cls_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
return v_res_1912_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1913_; double v___x_1914_; 
v___x_1913_ = lean_unsigned_to_nat(0u);
v___x_1914_ = lean_float_of_nat(v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(lean_object* v_cls_1918_, lean_object* v_msg_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_ref_1925_; lean_object* v___x_1926_; lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1971_; 
v_ref_1925_ = lean_ctor_get(v___y_1922_, 5);
v___x_1926_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1929_ = v___x_1926_;
v_isShared_1930_ = v_isSharedCheck_1971_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1971_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v_traceState_1932_; lean_object* v_env_1933_; lean_object* v_nextMacroScope_1934_; lean_object* v_ngen_1935_; lean_object* v_auxDeclNGen_1936_; lean_object* v_cache_1937_; lean_object* v_messages_1938_; lean_object* v_infoState_1939_; lean_object* v_snapshotTasks_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1970_; 
v___x_1931_ = lean_st_ref_take(v___y_1923_);
v_traceState_1932_ = lean_ctor_get(v___x_1931_, 4);
v_env_1933_ = lean_ctor_get(v___x_1931_, 0);
v_nextMacroScope_1934_ = lean_ctor_get(v___x_1931_, 1);
v_ngen_1935_ = lean_ctor_get(v___x_1931_, 2);
v_auxDeclNGen_1936_ = lean_ctor_get(v___x_1931_, 3);
v_cache_1937_ = lean_ctor_get(v___x_1931_, 5);
v_messages_1938_ = lean_ctor_get(v___x_1931_, 6);
v_infoState_1939_ = lean_ctor_get(v___x_1931_, 7);
v_snapshotTasks_1940_ = lean_ctor_get(v___x_1931_, 8);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1942_ = v___x_1931_;
v_isShared_1943_ = v_isSharedCheck_1970_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_snapshotTasks_1940_);
lean_inc(v_infoState_1939_);
lean_inc(v_messages_1938_);
lean_inc(v_cache_1937_);
lean_inc(v_traceState_1932_);
lean_inc(v_auxDeclNGen_1936_);
lean_inc(v_ngen_1935_);
lean_inc(v_nextMacroScope_1934_);
lean_inc(v_env_1933_);
lean_dec(v___x_1931_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1970_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
uint64_t v_tid_1944_; lean_object* v_traces_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1969_; 
v_tid_1944_ = lean_ctor_get_uint64(v_traceState_1932_, sizeof(void*)*1);
v_traces_1945_ = lean_ctor_get(v_traceState_1932_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_traceState_1932_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1947_ = v_traceState_1932_;
v_isShared_1948_ = v_isSharedCheck_1969_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_traces_1945_);
lean_dec(v_traceState_1932_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1969_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; double v___x_1950_; uint8_t v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1949_ = lean_box(0);
v___x_1950_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0);
v___x_1951_ = 0;
v___x_1952_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__1));
v___x_1953_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1953_, 0, v_cls_1918_);
lean_ctor_set(v___x_1953_, 1, v___x_1949_);
lean_ctor_set(v___x_1953_, 2, v___x_1952_);
lean_ctor_set_float(v___x_1953_, sizeof(void*)*3, v___x_1950_);
lean_ctor_set_float(v___x_1953_, sizeof(void*)*3 + 8, v___x_1950_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 16, v___x_1951_);
v___x_1954_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__2));
v___x_1955_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v_a_1927_);
lean_ctor_set(v___x_1955_, 2, v___x_1954_);
lean_inc(v_ref_1925_);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v_ref_1925_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = l_Lean_PersistentArray_push___redArg(v_traces_1945_, v___x_1956_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1957_);
v___x_1959_ = v___x_1947_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1957_);
lean_ctor_set_uint64(v_reuseFailAlloc_1968_, sizeof(void*)*1, v_tid_1944_);
v___x_1959_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1961_; 
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v___x_1959_);
v___x_1961_ = v___x_1942_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_env_1933_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_nextMacroScope_1934_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_ngen_1935_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_auxDeclNGen_1936_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1967_, 5, v_cache_1937_);
lean_ctor_set(v_reuseFailAlloc_1967_, 6, v_messages_1938_);
lean_ctor_set(v_reuseFailAlloc_1967_, 7, v_infoState_1939_);
lean_ctor_set(v_reuseFailAlloc_1967_, 8, v_snapshotTasks_1940_);
v___x_1961_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1962_ = lean_st_ref_set(v___y_1923_, v___x_1961_);
v___x_1963_ = lean_box(0);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v___x_1963_);
v___x_1965_ = v___x_1929_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___boxed(lean_object* v_cls_1972_, lean_object* v_msg_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_1972_, v_msg_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
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
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__7));
v___x_1996_ = l_Lean_stringToMessageData(v___x_1995_);
return v___x_1996_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10(void){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__9));
v___x_1999_ = l_Lean_stringToMessageData(v___x_1998_);
return v___x_1999_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__11));
v___x_2002_ = l_Lean_stringToMessageData(v___x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(lean_object* v_ctorName_2003_, lean_object* v_mvarId_2004_, lean_object* v_h_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v_cls_2031_; lean_object* v___x_2032_; lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2053_; 
v_cls_2031_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_2032_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_2031_, v_a_2008_);
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2035_ = v___x_2032_;
v_isShared_2036_ = v_isSharedCheck_2053_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2053_;
goto v_resetjp_2034_;
}
v___jp_2011_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = lean_box(0);
v___x_2017_ = l_Lean_Meta_injection(v_mvarId_2004_, v_h_2005_, v___x_2016_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref(v___x_2017_);
if (lean_obj_tag(v_a_2018_) == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_dec(v_ctorName_2003_);
v___x_2019_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__3);
v___x_2020_ = l_panic___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__0(v___x_2019_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
return v___x_2020_;
}
else
{
lean_object* v_mvarId_2021_; lean_object* v___x_2022_; 
v_mvarId_2021_ = lean_ctor_get(v_a_2018_, 0);
lean_inc(v_mvarId_2021_);
lean_dec_ref(v_a_2018_);
v___x_2022_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_mvarId_2021_, v_ctorName_2003_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
return v___x_2022_;
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec(v_ctorName_2003_);
v_a_2023_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2017_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2017_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
v_resetjp_2034_:
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_unbox(v_a_2033_);
lean_dec(v_a_2033_);
if (v___x_2037_ == 0)
{
lean_del_object(v___x_2035_);
v___y_2012_ = v_a_2006_;
v___y_2013_ = v_a_2007_;
v___y_2014_ = v_a_2008_;
v___y_2015_ = v_a_2009_;
goto v___jp_2011_;
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2038_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__8);
lean_inc(v_ctorName_2003_);
v___x_2039_ = l_Lean_MessageData_ofName(v_ctorName_2003_);
v___x_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2038_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v___x_2041_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__10);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
lean_inc(v_h_2005_);
v___x_2043_ = l_Lean_mkFVar(v_h_2005_);
v___x_2044_ = l_Lean_MessageData_ofExpr(v___x_2043_);
v___x_2045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2042_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12, &l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__12);
v___x_2047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2045_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
lean_inc(v_mvarId_2004_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set_tag(v___x_2035_, 1);
lean_ctor_set(v___x_2035_, 0, v_mvarId_2004_);
v___x_2049_ = v___x_2035_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_mvarId_2004_);
v___x_2049_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2047_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_2031_, v___x_2050_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_dec_ref(v___x_2051_);
v___y_2012_ = v_a_2006_;
v___y_2013_ = v_a_2007_;
v___y_2014_ = v_a_2008_;
v___y_2015_ = v_a_2009_;
goto v___jp_2011_;
}
else
{
lean_dec(v_h_2005_);
lean_dec(v_mvarId_2004_);
lean_dec(v_ctorName_2003_);
return v___x_2051_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___boxed(lean_object* v_ctorName_2054_, lean_object* v_mvarId_2055_, lean_object* v_h_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2054_, v_mvarId_2055_, v_h_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(lean_object* v_type_2063_, lean_object* v_k_2064_, uint8_t v_cleanupAnnotations_2065_, uint8_t v_whnfType_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v___f_2072_; lean_object* v___x_2073_; 
v___f_2072_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2072_, 0, v_k_2064_);
v___x_2073_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2063_, v___f_2072_, v_cleanupAnnotations_2065_, v_whnfType_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_a_2082_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2073_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2073_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg___boxed(lean_object* v_type_2090_, lean_object* v_k_2091_, lean_object* v_cleanupAnnotations_2092_, lean_object* v_whnfType_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2099_; uint8_t v_whnfType_boxed_2100_; lean_object* v_res_2101_; 
v_cleanupAnnotations_boxed_2099_ = lean_unbox(v_cleanupAnnotations_2092_);
v_whnfType_boxed_2100_ = lean_unbox(v_whnfType_2093_);
v_res_2101_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2090_, v_k_2091_, v_cleanupAnnotations_boxed_2099_, v_whnfType_boxed_2100_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(lean_object* v_00_u03b1_2102_, lean_object* v_type_2103_, lean_object* v_k_2104_, uint8_t v_cleanupAnnotations_2105_, uint8_t v_whnfType_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_type_2103_, v_k_2104_, v_cleanupAnnotations_2105_, v_whnfType_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_type_2114_, lean_object* v_k_2115_, lean_object* v_cleanupAnnotations_2116_, lean_object* v_whnfType_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2123_; uint8_t v_whnfType_boxed_2124_; lean_object* v_res_2125_; 
v_cleanupAnnotations_boxed_2123_ = lean_unbox(v_cleanupAnnotations_2116_);
v_whnfType_boxed_2124_ = lean_unbox(v_whnfType_2117_);
v_res_2125_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0(v_00_u03b1_2113_, v_type_2114_, v_k_2115_, v_cleanupAnnotations_boxed_2123_, v_whnfType_boxed_2124_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(lean_object* v___x_2126_, lean_object* v_ctorName_2127_, lean_object* v_xs_2128_, lean_object* v_type_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_box(0);
v___x_2136_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2129_, v___x_2135_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref(v___x_2136_);
v___x_2138_ = l_Lean_Expr_mvarId_x21(v_a_2137_);
v___x_2139_ = lean_array_get_size(v_xs_2128_);
v___x_2140_ = lean_unsigned_to_nat(1u);
v___x_2141_ = lean_nat_sub(v___x_2139_, v___x_2140_);
v___x_2142_ = lean_array_get_borrowed(v___x_2126_, v_xs_2128_, v___x_2141_);
lean_dec(v___x_2141_);
v___x_2143_ = l_Lean_Expr_fvarId_x21(v___x_2142_);
v___x_2144_ = l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq(v_ctorName_2127_, v___x_2138_, v___x_2143_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2144_) == 0)
{
uint8_t v___x_2145_; uint8_t v___x_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; 
lean_dec_ref(v___x_2144_);
v___x_2145_ = 0;
v___x_2146_ = 1;
v___x_2147_ = 1;
v___x_2148_ = l_Lean_Meta_mkLambdaFVars(v_xs_2128_, v_a_2137_, v___x_2145_, v___x_2146_, v___x_2145_, v___x_2146_, v___x_2147_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
return v___x_2148_;
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_a_2137_);
v_a_2149_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2144_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2144_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_dec(v_ctorName_2127_);
lean_dec_ref(v___x_2126_);
return v___x_2136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed(lean_object* v___x_2157_, lean_object* v_ctorName_2158_, lean_object* v_xs_2159_, lean_object* v_type_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0(v___x_2157_, v_ctorName_2158_, v_xs_2159_, v_type_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec_ref(v_xs_2159_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(lean_object* v_ctorName_2167_, lean_object* v_targetType_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___x_2174_; lean_object* v___f_2175_; uint8_t v___x_2176_; lean_object* v___x_2177_; 
v___x_2174_ = l_Lean_instInhabitedExpr;
v___f_2175_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2175_, 0, v___x_2174_);
lean_closure_set(v___f_2175_, 1, v_ctorName_2167_);
v___x_2176_ = 0;
v___x_2177_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_2168_, v___f_2175_, v___x_2176_, v___x_2176_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue___boxed(lean_object* v_ctorName_2178_, lean_object* v_targetType_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_ctorName_2178_, v_targetType_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
lean_dec(v_a_2183_);
lean_dec_ref(v_a_2182_);
lean_dec(v_a_2181_);
lean_dec_ref(v_a_2180_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheoremNameFor(lean_object* v_ctorName_2189_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheoremNameFor___closed__1));
v___x_2191_ = l_Lean_Name_append(v_ctorName_2189_, v___x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(lean_object* v_e_2192_, lean_object* v___y_2193_){
_start:
{
uint8_t v___x_2195_; 
v___x_2195_ = l_Lean_Expr_hasMVar(v_e_2192_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2196_, 0, v_e_2192_);
return v___x_2196_;
}
else
{
lean_object* v___x_2197_; lean_object* v_mctx_2198_; lean_object* v___x_2199_; lean_object* v_fst_2200_; lean_object* v_snd_2201_; lean_object* v___x_2202_; lean_object* v_cache_2203_; lean_object* v_zetaDeltaFVarIds_2204_; lean_object* v_postponed_2205_; lean_object* v_diag_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2215_; 
v___x_2197_ = lean_st_ref_get(v___y_2193_);
v_mctx_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc_ref(v_mctx_2198_);
lean_dec(v___x_2197_);
v___x_2199_ = l_Lean_instantiateMVarsCore(v_mctx_2198_, v_e_2192_);
v_fst_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_fst_2200_);
v_snd_2201_ = lean_ctor_get(v___x_2199_, 1);
lean_inc(v_snd_2201_);
lean_dec_ref(v___x_2199_);
v___x_2202_ = lean_st_ref_take(v___y_2193_);
v_cache_2203_ = lean_ctor_get(v___x_2202_, 1);
v_zetaDeltaFVarIds_2204_ = lean_ctor_get(v___x_2202_, 2);
v_postponed_2205_ = lean_ctor_get(v___x_2202_, 3);
v_diag_2206_ = lean_ctor_get(v___x_2202_, 4);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; 
v_unused_2216_ = lean_ctor_get(v___x_2202_, 0);
lean_dec(v_unused_2216_);
v___x_2208_ = v___x_2202_;
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_diag_2206_);
lean_inc(v_postponed_2205_);
lean_inc(v_zetaDeltaFVarIds_2204_);
lean_inc(v_cache_2203_);
lean_dec(v___x_2202_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v_snd_2201_);
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_snd_2201_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_cache_2203_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_zetaDeltaFVarIds_2204_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v_postponed_2205_);
lean_ctor_set(v_reuseFailAlloc_2214_, 4, v_diag_2206_);
v___x_2211_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_st_ref_set(v___y_2193_, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_fst_2200_);
return v___x_2213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg___boxed(lean_object* v_e_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2217_, v___y_2218_);
lean_dec(v___y_2218_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(lean_object* v_e_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_e_2221_, v___y_2223_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___boxed(lean_object* v_e_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0(v_e_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
return v_res_2234_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = lean_unsigned_to_nat(32u);
v___x_2236_ = lean_mk_empty_array_with_capacity(v___x_2235_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2238_ = ((size_t)5ULL);
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = lean_unsigned_to_nat(32u);
v___x_2241_ = lean_mk_empty_array_with_capacity(v___x_2240_);
v___x_2242_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__0);
v___x_2243_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
lean_ctor_set(v___x_2243_, 1, v___x_2241_);
lean_ctor_set(v___x_2243_, 2, v___x_2239_);
lean_ctor_set(v___x_2243_, 3, v___x_2239_);
lean_ctor_set_usize(v___x_2243_, 4, v___x_2238_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; lean_object* v_traceState_2247_; lean_object* v_traces_2248_; lean_object* v___x_2249_; lean_object* v_traceState_2250_; lean_object* v_env_2251_; lean_object* v_nextMacroScope_2252_; lean_object* v_ngen_2253_; lean_object* v_auxDeclNGen_2254_; lean_object* v_cache_2255_; lean_object* v_messages_2256_; lean_object* v_infoState_2257_; lean_object* v_snapshotTasks_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2277_; 
v___x_2246_ = lean_st_ref_get(v___y_2244_);
v_traceState_2247_ = lean_ctor_get(v___x_2246_, 4);
lean_inc_ref(v_traceState_2247_);
lean_dec(v___x_2246_);
v_traces_2248_ = lean_ctor_get(v_traceState_2247_, 0);
lean_inc_ref(v_traces_2248_);
lean_dec_ref(v_traceState_2247_);
v___x_2249_ = lean_st_ref_take(v___y_2244_);
v_traceState_2250_ = lean_ctor_get(v___x_2249_, 4);
v_env_2251_ = lean_ctor_get(v___x_2249_, 0);
v_nextMacroScope_2252_ = lean_ctor_get(v___x_2249_, 1);
v_ngen_2253_ = lean_ctor_get(v___x_2249_, 2);
v_auxDeclNGen_2254_ = lean_ctor_get(v___x_2249_, 3);
v_cache_2255_ = lean_ctor_get(v___x_2249_, 5);
v_messages_2256_ = lean_ctor_get(v___x_2249_, 6);
v_infoState_2257_ = lean_ctor_get(v___x_2249_, 7);
v_snapshotTasks_2258_ = lean_ctor_get(v___x_2249_, 8);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2260_ = v___x_2249_;
v_isShared_2261_ = v_isSharedCheck_2277_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_snapshotTasks_2258_);
lean_inc(v_infoState_2257_);
lean_inc(v_messages_2256_);
lean_inc(v_cache_2255_);
lean_inc(v_traceState_2250_);
lean_inc(v_auxDeclNGen_2254_);
lean_inc(v_ngen_2253_);
lean_inc(v_nextMacroScope_2252_);
lean_inc(v_env_2251_);
lean_dec(v___x_2249_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2277_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
uint64_t v_tid_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2275_; 
v_tid_2262_ = lean_ctor_get_uint64(v_traceState_2250_, sizeof(void*)*1);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_traceState_2250_);
if (v_isSharedCheck_2275_ == 0)
{
lean_object* v_unused_2276_; 
v_unused_2276_ = lean_ctor_get(v_traceState_2250_, 0);
lean_dec(v_unused_2276_);
v___x_2264_ = v_traceState_2250_;
v_isShared_2265_ = v_isSharedCheck_2275_;
goto v_resetjp_2263_;
}
else
{
lean_dec(v_traceState_2250_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2275_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
v___x_2266_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___closed__1);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2266_);
v___x_2268_ = v___x_2264_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2266_);
lean_ctor_set_uint64(v_reuseFailAlloc_2274_, sizeof(void*)*1, v_tid_2262_);
v___x_2268_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2270_; 
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 4, v___x_2268_);
v___x_2270_ = v___x_2260_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_env_2251_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_nextMacroScope_2252_);
lean_ctor_set(v_reuseFailAlloc_2273_, 2, v_ngen_2253_);
lean_ctor_set(v_reuseFailAlloc_2273_, 3, v_auxDeclNGen_2254_);
lean_ctor_set(v_reuseFailAlloc_2273_, 4, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2273_, 5, v_cache_2255_);
lean_ctor_set(v_reuseFailAlloc_2273_, 6, v_messages_2256_);
lean_ctor_set(v_reuseFailAlloc_2273_, 7, v_infoState_2257_);
lean_ctor_set(v_reuseFailAlloc_2273_, 8, v_snapshotTasks_2258_);
v___x_2270_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_st_ref_set(v___y_2244_, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v_traces_2248_);
return v___x_2272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg___boxed(lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2278_);
lean_dec(v___y_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v___y_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___boxed(lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1(v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(lean_object* v_opts_2293_, lean_object* v_opt_2294_){
_start:
{
lean_object* v_name_2295_; lean_object* v_defValue_2296_; lean_object* v_map_2297_; lean_object* v___x_2298_; 
v_name_2295_ = lean_ctor_get(v_opt_2294_, 0);
v_defValue_2296_ = lean_ctor_get(v_opt_2294_, 1);
v_map_2297_ = lean_ctor_get(v_opts_2293_, 0);
v___x_2298_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2297_, v_name_2295_);
if (lean_obj_tag(v___x_2298_) == 0)
{
uint8_t v___x_2299_; 
v___x_2299_ = lean_unbox(v_defValue_2296_);
return v___x_2299_;
}
else
{
lean_object* v_val_2300_; 
v_val_2300_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_val_2300_);
lean_dec_ref(v___x_2298_);
if (lean_obj_tag(v_val_2300_) == 1)
{
uint8_t v_v_2301_; 
v_v_2301_ = lean_ctor_get_uint8(v_val_2300_, 0);
lean_dec_ref(v_val_2300_);
return v_v_2301_;
}
else
{
uint8_t v___x_2302_; 
lean_dec(v_val_2300_);
v___x_2302_ = lean_unbox(v_defValue_2296_);
return v___x_2302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2___boxed(lean_object* v_opts_2303_, lean_object* v_opt_2304_){
_start:
{
uint8_t v_res_2305_; lean_object* v_r_2306_; 
v_res_2305_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2303_, v_opt_2304_);
lean_dec_ref(v_opt_2304_);
lean_dec_ref(v_opts_2303_);
v_r_2306_ = lean_box(v_res_2305_);
return v_r_2306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__0));
v___x_2309_ = l_Lean_stringToMessageData(v___x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(lean_object* v_name_2310_, lean_object* v_x_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2317_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___closed__1);
v___x_2318_ = l_Lean_MessageData_ofName(v_name_2310_);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed(lean_object* v_name_2323_, lean_object* v_x_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0(v_name_2323_, v_x_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec_ref(v_x_2324_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(lean_object* v_name_2331_, lean_object* v_val_2332_, lean_object* v_name_2333_, lean_object* v_levelParams_2334_, uint8_t v___x_2335_, lean_object* v_____r_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
lean_inc_ref(v_val_2332_);
v___x_2342_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2331_, v_val_2332_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2344_; lean_object* v_a_2345_; lean_object* v___x_2346_; lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2359_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2332_, v___y_2338_);
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref(v___x_2344_);
v___x_2346_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2343_, v___y_2338_);
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2359_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2359_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_inc(v_name_2333_);
v___x_2351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2351_, 0, v_name_2333_);
lean_ctor_set(v___x_2351_, 1, v_levelParams_2334_);
lean_ctor_set(v___x_2351_, 2, v_a_2345_);
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2353_, 0, v_name_2333_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
v___x_2354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2351_);
lean_ctor_set(v___x_2354_, 1, v_a_2347_);
lean_ctor_set(v___x_2354_, 2, v___x_2353_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set_tag(v___x_2349_, 2);
lean_ctor_set(v___x_2349_, 0, v___x_2354_);
v___x_2356_ = v___x_2349_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_addDecl(v___x_2356_, v___x_2335_, v___y_2339_, v___y_2340_);
return v___x_2357_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_levelParams_2334_);
lean_dec(v_name_2333_);
lean_dec_ref(v_val_2332_);
v_a_2360_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2342_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2342_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1___boxed(lean_object* v_name_2368_, lean_object* v_val_2369_, lean_object* v_name_2370_, lean_object* v_levelParams_2371_, lean_object* v___x_2372_, lean_object* v_____r_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
uint8_t v___x_10672__boxed_2379_; lean_object* v_res_2380_; 
v___x_10672__boxed_2379_ = lean_unbox(v___x_2372_);
v_res_2380_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2368_, v_val_2369_, v_name_2370_, v_levelParams_2371_, v___x_10672__boxed_2379_, v_____r_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(lean_object* v_name_2381_, lean_object* v_val_2382_, lean_object* v_name_2383_, lean_object* v_levelParams_2384_, lean_object* v_____r_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v___x_2391_; 
lean_inc_ref(v_val_2382_);
v___x_2391_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2381_, v_val_2382_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; lean_object* v_a_2394_; lean_object* v___x_2395_; lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2409_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref(v___x_2391_);
v___x_2393_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2382_, v___y_2387_);
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref(v___x_2393_);
v___x_2395_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2392_, v___y_2387_);
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2409_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2409_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
lean_inc(v_name_2383_);
v___x_2400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2400_, 0, v_name_2383_);
lean_ctor_set(v___x_2400_, 1, v_levelParams_2384_);
lean_ctor_set(v___x_2400_, 2, v_a_2394_);
v___x_2401_ = lean_box(0);
v___x_2402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_name_2383_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2400_);
lean_ctor_set(v___x_2403_, 1, v_a_2396_);
lean_ctor_set(v___x_2403_, 2, v___x_2402_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set_tag(v___x_2398_, 2);
lean_ctor_set(v___x_2398_, 0, v___x_2403_);
v___x_2405_ = v___x_2398_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
uint8_t v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = 0;
v___x_2407_ = l_Lean_addDecl(v___x_2405_, v___x_2406_, v___y_2388_, v___y_2389_);
return v___x_2407_;
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v_levelParams_2384_);
lean_dec(v_name_2383_);
lean_dec_ref(v_val_2382_);
v_a_2410_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2391_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2391_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2___boxed(lean_object* v_name_2418_, lean_object* v_val_2419_, lean_object* v_name_2420_, lean_object* v_levelParams_2421_, lean_object* v_____r_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2418_, v_val_2419_, v_name_2420_, v_levelParams_2421_, v_____r_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2428_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(lean_object* v_e_2429_){
_start:
{
if (lean_obj_tag(v_e_2429_) == 0)
{
uint8_t v___x_2430_; 
v___x_2430_ = 2;
return v___x_2430_;
}
else
{
uint8_t v___x_2431_; 
v___x_2431_ = 0;
return v___x_2431_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3___boxed(lean_object* v_e_2432_){
_start:
{
uint8_t v_res_2433_; lean_object* v_r_2434_; 
v_res_2433_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_e_2432_);
lean_dec_ref(v_e_2432_);
v_r_2434_ = lean_box(v_res_2433_);
return v_r_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(lean_object* v_opts_2435_, lean_object* v_opt_2436_){
_start:
{
lean_object* v_name_2437_; lean_object* v_defValue_2438_; lean_object* v_map_2439_; lean_object* v___x_2440_; 
v_name_2437_ = lean_ctor_get(v_opt_2436_, 0);
v_defValue_2438_ = lean_ctor_get(v_opt_2436_, 1);
v_map_2439_ = lean_ctor_get(v_opts_2435_, 0);
v___x_2440_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2439_, v_name_2437_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_inc(v_defValue_2438_);
return v_defValue_2438_;
}
else
{
lean_object* v_val_2441_; 
v_val_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_val_2441_);
lean_dec_ref(v___x_2440_);
if (lean_obj_tag(v_val_2441_) == 3)
{
lean_object* v_v_2442_; 
v_v_2442_ = lean_ctor_get(v_val_2441_, 0);
lean_inc(v_v_2442_);
lean_dec_ref(v_val_2441_);
return v_v_2442_;
}
else
{
lean_dec(v_val_2441_);
lean_inc(v_defValue_2438_);
return v_defValue_2438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6___boxed(lean_object* v_opts_2443_, lean_object* v_opt_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2443_, v_opt_2444_);
lean_dec_ref(v_opt_2444_);
lean_dec_ref(v_opts_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(lean_object* v_x_2446_){
_start:
{
if (lean_obj_tag(v_x_2446_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
v_a_2448_ = lean_ctor_get(v_x_2446_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_x_2446_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v_x_2446_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v_x_2446_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set_tag(v___x_2450_, 1);
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
v_a_2456_ = lean_ctor_get(v_x_2446_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_x_2446_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v_x_2446_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v_x_2446_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set_tag(v___x_2458_, 0);
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg___boxed(lean_object* v_x_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2464_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(size_t v_sz_2467_, size_t v_i_2468_, lean_object* v_bs_2469_){
_start:
{
uint8_t v___x_2470_; 
v___x_2470_ = lean_usize_dec_lt(v_i_2468_, v_sz_2467_);
if (v___x_2470_ == 0)
{
return v_bs_2469_;
}
else
{
lean_object* v_v_2471_; lean_object* v_msg_2472_; lean_object* v___x_2473_; lean_object* v_bs_x27_2474_; size_t v___x_2475_; size_t v___x_2476_; lean_object* v___x_2477_; 
v_v_2471_ = lean_array_uget_borrowed(v_bs_2469_, v_i_2468_);
v_msg_2472_ = lean_ctor_get(v_v_2471_, 1);
lean_inc_ref(v_msg_2472_);
v___x_2473_ = lean_unsigned_to_nat(0u);
v_bs_x27_2474_ = lean_array_uset(v_bs_2469_, v_i_2468_, v___x_2473_);
v___x_2475_ = ((size_t)1ULL);
v___x_2476_ = lean_usize_add(v_i_2468_, v___x_2475_);
v___x_2477_ = lean_array_uset(v_bs_x27_2474_, v_i_2468_, v_msg_2472_);
v_i_2468_ = v___x_2476_;
v_bs_2469_ = v___x_2477_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_2479_, lean_object* v_i_2480_, lean_object* v_bs_2481_){
_start:
{
size_t v_sz_boxed_2482_; size_t v_i_boxed_2483_; lean_object* v_res_2484_; 
v_sz_boxed_2482_ = lean_unbox_usize(v_sz_2479_);
lean_dec(v_sz_2479_);
v_i_boxed_2483_ = lean_unbox_usize(v_i_2480_);
lean_dec(v_i_2480_);
v_res_2484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_boxed_2482_, v_i_boxed_2483_, v_bs_2481_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(lean_object* v_oldTraces_2485_, lean_object* v_data_2486_, lean_object* v_ref_2487_, lean_object* v_msg_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_fileName_2494_; lean_object* v_fileMap_2495_; lean_object* v_options_2496_; lean_object* v_currRecDepth_2497_; lean_object* v_maxRecDepth_2498_; lean_object* v_ref_2499_; lean_object* v_currNamespace_2500_; lean_object* v_openDecls_2501_; lean_object* v_initHeartbeats_2502_; lean_object* v_maxHeartbeats_2503_; lean_object* v_quotContext_2504_; lean_object* v_currMacroScope_2505_; uint8_t v_diag_2506_; lean_object* v_cancelTk_x3f_2507_; uint8_t v_suppressElabErrors_2508_; lean_object* v_inheritedTraceOptions_2509_; lean_object* v___x_2510_; lean_object* v_traceState_2511_; lean_object* v_traces_2512_; lean_object* v_ref_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; size_t v_sz_2516_; size_t v___x_2517_; lean_object* v___x_2518_; lean_object* v_msg_2519_; lean_object* v___x_2520_; lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2558_; 
v_fileName_2494_ = lean_ctor_get(v___y_2491_, 0);
v_fileMap_2495_ = lean_ctor_get(v___y_2491_, 1);
v_options_2496_ = lean_ctor_get(v___y_2491_, 2);
v_currRecDepth_2497_ = lean_ctor_get(v___y_2491_, 3);
v_maxRecDepth_2498_ = lean_ctor_get(v___y_2491_, 4);
v_ref_2499_ = lean_ctor_get(v___y_2491_, 5);
v_currNamespace_2500_ = lean_ctor_get(v___y_2491_, 6);
v_openDecls_2501_ = lean_ctor_get(v___y_2491_, 7);
v_initHeartbeats_2502_ = lean_ctor_get(v___y_2491_, 8);
v_maxHeartbeats_2503_ = lean_ctor_get(v___y_2491_, 9);
v_quotContext_2504_ = lean_ctor_get(v___y_2491_, 10);
v_currMacroScope_2505_ = lean_ctor_get(v___y_2491_, 11);
v_diag_2506_ = lean_ctor_get_uint8(v___y_2491_, sizeof(void*)*14);
v_cancelTk_x3f_2507_ = lean_ctor_get(v___y_2491_, 12);
v_suppressElabErrors_2508_ = lean_ctor_get_uint8(v___y_2491_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2509_ = lean_ctor_get(v___y_2491_, 13);
v___x_2510_ = lean_st_ref_get(v___y_2492_);
v_traceState_2511_ = lean_ctor_get(v___x_2510_, 4);
lean_inc_ref(v_traceState_2511_);
lean_dec(v___x_2510_);
v_traces_2512_ = lean_ctor_get(v_traceState_2511_, 0);
lean_inc_ref(v_traces_2512_);
lean_dec_ref(v_traceState_2511_);
v_ref_2513_ = l_Lean_replaceRef(v_ref_2487_, v_ref_2499_);
lean_inc_ref(v_inheritedTraceOptions_2509_);
lean_inc(v_cancelTk_x3f_2507_);
lean_inc(v_currMacroScope_2505_);
lean_inc(v_quotContext_2504_);
lean_inc(v_maxHeartbeats_2503_);
lean_inc(v_initHeartbeats_2502_);
lean_inc(v_openDecls_2501_);
lean_inc(v_currNamespace_2500_);
lean_inc(v_maxRecDepth_2498_);
lean_inc(v_currRecDepth_2497_);
lean_inc_ref(v_options_2496_);
lean_inc_ref(v_fileMap_2495_);
lean_inc_ref(v_fileName_2494_);
v___x_2514_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2514_, 0, v_fileName_2494_);
lean_ctor_set(v___x_2514_, 1, v_fileMap_2495_);
lean_ctor_set(v___x_2514_, 2, v_options_2496_);
lean_ctor_set(v___x_2514_, 3, v_currRecDepth_2497_);
lean_ctor_set(v___x_2514_, 4, v_maxRecDepth_2498_);
lean_ctor_set(v___x_2514_, 5, v_ref_2513_);
lean_ctor_set(v___x_2514_, 6, v_currNamespace_2500_);
lean_ctor_set(v___x_2514_, 7, v_openDecls_2501_);
lean_ctor_set(v___x_2514_, 8, v_initHeartbeats_2502_);
lean_ctor_set(v___x_2514_, 9, v_maxHeartbeats_2503_);
lean_ctor_set(v___x_2514_, 10, v_quotContext_2504_);
lean_ctor_set(v___x_2514_, 11, v_currMacroScope_2505_);
lean_ctor_set(v___x_2514_, 12, v_cancelTk_x3f_2507_);
lean_ctor_set(v___x_2514_, 13, v_inheritedTraceOptions_2509_);
lean_ctor_set_uint8(v___x_2514_, sizeof(void*)*14, v_diag_2506_);
lean_ctor_set_uint8(v___x_2514_, sizeof(void*)*14 + 1, v_suppressElabErrors_2508_);
v___x_2515_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2512_);
lean_dec_ref(v_traces_2512_);
v_sz_2516_ = lean_array_size(v___x_2515_);
v___x_2517_ = ((size_t)0ULL);
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4_spec__5(v_sz_2516_, v___x_2517_, v___x_2515_);
v_msg_2519_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2519_, 0, v_data_2486_);
lean_ctor_set(v_msg_2519_, 1, v_msg_2488_);
lean_ctor_set(v_msg_2519_, 2, v___x_2518_);
v___x_2520_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1_spec__1(v_msg_2519_, v___y_2489_, v___y_2490_, v___x_2514_, v___y_2492_);
lean_dec_ref(v___x_2514_);
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2558_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2558_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v_traceState_2526_; lean_object* v_env_2527_; lean_object* v_nextMacroScope_2528_; lean_object* v_ngen_2529_; lean_object* v_auxDeclNGen_2530_; lean_object* v_cache_2531_; lean_object* v_messages_2532_; lean_object* v_infoState_2533_; lean_object* v_snapshotTasks_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2557_; 
v___x_2525_ = lean_st_ref_take(v___y_2492_);
v_traceState_2526_ = lean_ctor_get(v___x_2525_, 4);
v_env_2527_ = lean_ctor_get(v___x_2525_, 0);
v_nextMacroScope_2528_ = lean_ctor_get(v___x_2525_, 1);
v_ngen_2529_ = lean_ctor_get(v___x_2525_, 2);
v_auxDeclNGen_2530_ = lean_ctor_get(v___x_2525_, 3);
v_cache_2531_ = lean_ctor_get(v___x_2525_, 5);
v_messages_2532_ = lean_ctor_get(v___x_2525_, 6);
v_infoState_2533_ = lean_ctor_get(v___x_2525_, 7);
v_snapshotTasks_2534_ = lean_ctor_get(v___x_2525_, 8);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2536_ = v___x_2525_;
v_isShared_2537_ = v_isSharedCheck_2557_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_snapshotTasks_2534_);
lean_inc(v_infoState_2533_);
lean_inc(v_messages_2532_);
lean_inc(v_cache_2531_);
lean_inc(v_traceState_2526_);
lean_inc(v_auxDeclNGen_2530_);
lean_inc(v_ngen_2529_);
lean_inc(v_nextMacroScope_2528_);
lean_inc(v_env_2527_);
lean_dec(v___x_2525_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2557_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
uint64_t v_tid_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2555_; 
v_tid_2538_ = lean_ctor_get_uint64(v_traceState_2526_, sizeof(void*)*1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_traceState_2526_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; 
v_unused_2556_ = lean_ctor_get(v_traceState_2526_, 0);
lean_dec(v_unused_2556_);
v___x_2540_ = v_traceState_2526_;
v_isShared_2541_ = v_isSharedCheck_2555_;
goto v_resetjp_2539_;
}
else
{
lean_dec(v_traceState_2526_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2555_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v_ref_2487_);
lean_ctor_set(v___x_2542_, 1, v_a_2521_);
v___x_2543_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2485_, v___x_2542_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2543_);
v___x_2545_ = v___x_2540_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2543_);
lean_ctor_set_uint64(v_reuseFailAlloc_2554_, sizeof(void*)*1, v_tid_2538_);
v___x_2545_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2547_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 4, v___x_2545_);
v___x_2547_ = v___x_2536_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_env_2527_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_nextMacroScope_2528_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_ngen_2529_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_auxDeclNGen_2530_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2553_, 5, v_cache_2531_);
lean_ctor_set(v_reuseFailAlloc_2553_, 6, v_messages_2532_);
lean_ctor_set(v_reuseFailAlloc_2553_, 7, v_infoState_2533_);
lean_ctor_set(v_reuseFailAlloc_2553_, 8, v_snapshotTasks_2534_);
v___x_2547_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2548_ = lean_st_ref_set(v___y_2492_, v___x_2547_);
v___x_2549_ = lean_box(0);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v___x_2549_);
v___x_2551_ = v___x_2523_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4___boxed(lean_object* v_oldTraces_2559_, lean_object* v_data_2560_, lean_object* v_ref_2561_, lean_object* v_msg_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2559_, v_data_2560_, v_ref_2561_, v_msg_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
return v_res_2568_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__0));
v___x_2571_ = l_Lean_stringToMessageData(v___x_2570_);
return v___x_2571_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__2));
v___x_2574_ = l_Lean_stringToMessageData(v___x_2573_);
return v___x_2574_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2575_; double v___x_2576_; 
v___x_2575_ = lean_unsigned_to_nat(1000u);
v___x_2576_ = lean_float_of_nat(v___x_2575_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(lean_object* v_cls_2577_, uint8_t v_collapsed_2578_, lean_object* v_tag_2579_, lean_object* v_opts_2580_, uint8_t v_clsEnabled_2581_, lean_object* v_oldTraces_2582_, lean_object* v_msg_2583_, lean_object* v_resStartStop_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_fst_2590_; lean_object* v_snd_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2681_; 
v_fst_2590_ = lean_ctor_get(v_resStartStop_2584_, 0);
v_snd_2591_ = lean_ctor_get(v_resStartStop_2584_, 1);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_resStartStop_2584_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2593_ = v_resStartStop_2584_;
v_isShared_2594_ = v_isSharedCheck_2681_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_snd_2591_);
lean_inc(v_fst_2590_);
lean_dec(v_resStartStop_2584_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2681_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v_data_2598_; lean_object* v_fst_2601_; lean_object* v_snd_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2680_; 
v_fst_2601_ = lean_ctor_get(v_snd_2591_, 0);
v_snd_2602_ = lean_ctor_get(v_snd_2591_, 1);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_snd_2591_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2604_ = v_snd_2591_;
v_isShared_2605_ = v_isSharedCheck_2680_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_snd_2602_);
lean_inc(v_fst_2601_);
lean_dec(v_snd_2591_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2680_;
goto v_resetjp_2603_;
}
v___jp_2595_:
{
lean_object* v___x_2599_; 
lean_inc(v___y_2597_);
v___x_2599_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__4(v_oldTraces_2582_, v_data_2598_, v___y_2597_, v___y_2596_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v___x_2600_; 
lean_dec_ref(v___x_2599_);
v___x_2600_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2590_);
return v___x_2600_;
}
else
{
lean_dec(v_fst_2590_);
return v___x_2599_;
}
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; uint8_t v___x_2607_; lean_object* v___y_2609_; lean_object* v_a_2610_; uint8_t v___y_2634_; double v___y_2665_; 
v___x_2606_ = l_Lean_trace_profiler;
v___x_2607_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2580_, v___x_2606_);
if (v___x_2607_ == 0)
{
v___y_2634_ = v___x_2607_;
goto v___jp_2633_;
}
else
{
lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2671_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_opts_2580_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; double v___x_2674_; double v___x_2675_; double v___x_2676_; 
v___x_2672_ = l_Lean_trace_profiler_threshold;
v___x_2673_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2580_, v___x_2672_);
v___x_2674_ = lean_float_of_nat(v___x_2673_);
v___x_2675_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__4);
v___x_2676_ = lean_float_div(v___x_2674_, v___x_2675_);
v___y_2665_ = v___x_2676_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; double v___x_2679_; 
v___x_2677_ = l_Lean_trace_profiler_threshold;
v___x_2678_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__6(v_opts_2580_, v___x_2677_);
v___x_2679_ = lean_float_of_nat(v___x_2678_);
v___y_2665_ = v___x_2679_;
goto v___jp_2664_;
}
}
v___jp_2608_:
{
uint8_t v_result_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2616_; 
v_result_2611_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__3(v_fst_2590_);
v___x_2612_ = l_Lean_TraceResult_toEmoji(v_result_2611_);
v___x_2613_ = l_Lean_stringToMessageData(v___x_2612_);
v___x_2614_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__1);
if (v_isShared_2605_ == 0)
{
lean_ctor_set_tag(v___x_2604_, 7);
lean_ctor_set(v___x_2604_, 1, v___x_2614_);
lean_ctor_set(v___x_2604_, 0, v___x_2613_);
v___x_2616_ = v___x_2604_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v_m_2618_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 7);
lean_ctor_set(v___x_2593_, 1, v_a_2610_);
lean_ctor_set(v___x_2593_, 0, v___x_2616_);
v_m_2618_ = v___x_2593_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_a_2610_);
v_m_2618_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; double v___x_2621_; lean_object* v_data_2622_; 
v___x_2619_ = lean_box(v_result_2611_);
v___x_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
v___x_2621_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__0);
lean_inc_ref(v_tag_2579_);
lean_inc_ref(v___x_2620_);
lean_inc(v_cls_2577_);
v_data_2622_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2622_, 0, v_cls_2577_);
lean_ctor_set(v_data_2622_, 1, v___x_2620_);
lean_ctor_set(v_data_2622_, 2, v_tag_2579_);
lean_ctor_set_float(v_data_2622_, sizeof(void*)*3, v___x_2621_);
lean_ctor_set_float(v_data_2622_, sizeof(void*)*3 + 8, v___x_2621_);
lean_ctor_set_uint8(v_data_2622_, sizeof(void*)*3 + 16, v_collapsed_2578_);
if (v___x_2607_ == 0)
{
lean_dec_ref(v___x_2620_);
lean_dec(v_snd_2602_);
lean_dec(v_fst_2601_);
lean_dec_ref(v_tag_2579_);
lean_dec(v_cls_2577_);
v___y_2596_ = v_m_2618_;
v___y_2597_ = v___y_2609_;
v_data_2598_ = v_data_2622_;
goto v___jp_2595_;
}
else
{
lean_object* v_data_2623_; double v___x_2624_; double v___x_2625_; 
lean_dec_ref(v_data_2622_);
v_data_2623_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2623_, 0, v_cls_2577_);
lean_ctor_set(v_data_2623_, 1, v___x_2620_);
lean_ctor_set(v_data_2623_, 2, v_tag_2579_);
v___x_2624_ = lean_unbox_float(v_fst_2601_);
lean_dec(v_fst_2601_);
lean_ctor_set_float(v_data_2623_, sizeof(void*)*3, v___x_2624_);
v___x_2625_ = lean_unbox_float(v_snd_2602_);
lean_dec(v_snd_2602_);
lean_ctor_set_float(v_data_2623_, sizeof(void*)*3 + 8, v___x_2625_);
lean_ctor_set_uint8(v_data_2623_, sizeof(void*)*3 + 16, v_collapsed_2578_);
v___y_2596_ = v_m_2618_;
v___y_2597_ = v___y_2609_;
v_data_2598_ = v_data_2623_;
goto v___jp_2595_;
}
}
}
}
v___jp_2628_:
{
lean_object* v_ref_2629_; lean_object* v___x_2630_; 
v_ref_2629_ = lean_ctor_get(v___y_2587_, 5);
lean_inc(v___y_2588_);
lean_inc_ref(v___y_2587_);
lean_inc(v___y_2586_);
lean_inc_ref(v___y_2585_);
lean_inc(v_fst_2590_);
v___x_2630_ = lean_apply_6(v_msg_2583_, v_fst_2590_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, lean_box(0));
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref(v___x_2630_);
v___y_2609_ = v_ref_2629_;
v_a_2610_ = v_a_2631_;
goto v___jp_2608_;
}
else
{
lean_object* v___x_2632_; 
lean_dec_ref(v___x_2630_);
v___x_2632_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___closed__3);
v___y_2609_ = v_ref_2629_;
v_a_2610_ = v___x_2632_;
goto v___jp_2608_;
}
}
v___jp_2633_:
{
if (v_clsEnabled_2581_ == 0)
{
if (v___y_2634_ == 0)
{
lean_object* v___x_2635_; lean_object* v_traceState_2636_; lean_object* v_env_2637_; lean_object* v_nextMacroScope_2638_; lean_object* v_ngen_2639_; lean_object* v_auxDeclNGen_2640_; lean_object* v_cache_2641_; lean_object* v_messages_2642_; lean_object* v_infoState_2643_; lean_object* v_snapshotTasks_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2663_; 
lean_del_object(v___x_2604_);
lean_dec(v_snd_2602_);
lean_dec(v_fst_2601_);
lean_del_object(v___x_2593_);
lean_dec_ref(v_msg_2583_);
lean_dec_ref(v_tag_2579_);
lean_dec(v_cls_2577_);
v___x_2635_ = lean_st_ref_take(v___y_2588_);
v_traceState_2636_ = lean_ctor_get(v___x_2635_, 4);
v_env_2637_ = lean_ctor_get(v___x_2635_, 0);
v_nextMacroScope_2638_ = lean_ctor_get(v___x_2635_, 1);
v_ngen_2639_ = lean_ctor_get(v___x_2635_, 2);
v_auxDeclNGen_2640_ = lean_ctor_get(v___x_2635_, 3);
v_cache_2641_ = lean_ctor_get(v___x_2635_, 5);
v_messages_2642_ = lean_ctor_get(v___x_2635_, 6);
v_infoState_2643_ = lean_ctor_get(v___x_2635_, 7);
v_snapshotTasks_2644_ = lean_ctor_get(v___x_2635_, 8);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2646_ = v___x_2635_;
v_isShared_2647_ = v_isSharedCheck_2663_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_snapshotTasks_2644_);
lean_inc(v_infoState_2643_);
lean_inc(v_messages_2642_);
lean_inc(v_cache_2641_);
lean_inc(v_traceState_2636_);
lean_inc(v_auxDeclNGen_2640_);
lean_inc(v_ngen_2639_);
lean_inc(v_nextMacroScope_2638_);
lean_inc(v_env_2637_);
lean_dec(v___x_2635_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2663_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
uint64_t v_tid_2648_; lean_object* v_traces_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2662_; 
v_tid_2648_ = lean_ctor_get_uint64(v_traceState_2636_, sizeof(void*)*1);
v_traces_2649_ = lean_ctor_get(v_traceState_2636_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_traceState_2636_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2651_ = v_traceState_2636_;
v_isShared_2652_ = v_isSharedCheck_2662_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_traces_2649_);
lean_dec(v_traceState_2636_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2662_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2653_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2582_, v_traces_2649_);
lean_dec_ref(v_traces_2649_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2653_);
v___x_2655_ = v___x_2651_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2653_);
lean_ctor_set_uint64(v_reuseFailAlloc_2661_, sizeof(void*)*1, v_tid_2648_);
v___x_2655_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2657_; 
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 4, v___x_2655_);
v___x_2657_ = v___x_2646_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_env_2637_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_nextMacroScope_2638_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_ngen_2639_);
lean_ctor_set(v_reuseFailAlloc_2660_, 3, v_auxDeclNGen_2640_);
lean_ctor_set(v_reuseFailAlloc_2660_, 4, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2660_, 5, v_cache_2641_);
lean_ctor_set(v_reuseFailAlloc_2660_, 6, v_messages_2642_);
lean_ctor_set(v_reuseFailAlloc_2660_, 7, v_infoState_2643_);
lean_ctor_set(v_reuseFailAlloc_2660_, 8, v_snapshotTasks_2644_);
v___x_2657_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_st_ref_set(v___y_2588_, v___x_2657_);
v___x_2659_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_fst_2590_);
return v___x_2659_;
}
}
}
}
}
else
{
goto v___jp_2628_;
}
}
else
{
goto v___jp_2628_;
}
}
v___jp_2664_:
{
double v___x_2666_; double v___x_2667_; double v___x_2668_; uint8_t v___x_2669_; 
v___x_2666_ = lean_unbox_float(v_snd_2602_);
v___x_2667_ = lean_unbox_float(v_fst_2601_);
v___x_2668_ = lean_float_sub(v___x_2666_, v___x_2667_);
v___x_2669_ = lean_float_decLt(v___y_2665_, v___x_2668_);
v___y_2634_ = v___x_2669_;
goto v___jp_2633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3___boxed(lean_object* v_cls_2682_, lean_object* v_collapsed_2683_, lean_object* v_tag_2684_, lean_object* v_opts_2685_, lean_object* v_clsEnabled_2686_, lean_object* v_oldTraces_2687_, lean_object* v_msg_2688_, lean_object* v_resStartStop_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
uint8_t v_collapsed_boxed_2695_; uint8_t v_clsEnabled_boxed_2696_; lean_object* v_res_2697_; 
v_collapsed_boxed_2695_ = lean_unbox(v_collapsed_2683_);
v_clsEnabled_boxed_2696_ = lean_unbox(v_clsEnabled_2686_);
v_res_2697_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2682_, v_collapsed_boxed_2695_, v_tag_2684_, v_opts_2685_, v_clsEnabled_boxed_2696_, v_oldTraces_2687_, v_msg_2688_, v_resStartStop_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec_ref(v_opts_2685_);
return v_res_2697_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__0));
v___x_2700_ = l_Lean_stringToMessageData(v___x_2699_);
return v___x_2700_;
}
}
static double _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2(void){
_start:
{
lean_object* v___x_2701_; double v___x_2702_; 
v___x_2701_ = lean_unsigned_to_nat(1000000000u);
v___x_2702_ = lean_float_of_nat(v___x_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(lean_object* v_ctorVal_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_toConstantVal_2709_; lean_object* v_options_2710_; lean_object* v_name_2711_; lean_object* v_levelParams_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2950_; 
v_toConstantVal_2709_ = lean_ctor_get(v_ctorVal_2703_, 0);
lean_inc_ref(v_toConstantVal_2709_);
v_options_2710_ = lean_ctor_get(v_a_2706_, 2);
v_name_2711_ = lean_ctor_get(v_toConstantVal_2709_, 0);
v_levelParams_2712_ = lean_ctor_get(v_toConstantVal_2709_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_toConstantVal_2709_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; 
v_unused_2951_ = lean_ctor_get(v_toConstantVal_2709_, 2);
lean_dec(v_unused_2951_);
v___x_2714_ = v_toConstantVal_2709_;
v_isShared_2715_ = v_isSharedCheck_2950_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_levelParams_2712_);
lean_inc(v_name_2711_);
lean_dec(v_toConstantVal_2709_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2950_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
uint8_t v_hasTrace_2716_; lean_object* v_name_2717_; lean_object* v_cls_2718_; 
v_hasTrace_2716_ = lean_ctor_get_uint8(v_options_2710_, sizeof(void*)*1);
lean_inc(v_name_2711_);
v_name_2717_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_2711_);
v_cls_2718_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
if (v_hasTrace_2716_ == 0)
{
lean_object* v___x_2719_; 
v___x_2719_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2769_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2722_ = v___x_2719_;
v_isShared_2723_ = v_isSharedCheck_2769_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2769_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
if (lean_obj_tag(v_a_2720_) == 1)
{
lean_object* v_val_2724_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___x_2758_; lean_object* v_a_2759_; uint8_t v___x_2760_; 
lean_del_object(v___x_2722_);
v_val_2724_ = lean_ctor_get(v_a_2720_, 0);
lean_inc(v_val_2724_);
lean_dec_ref(v_a_2720_);
v___x_2758_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_2718_, v_a_2706_);
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref(v___x_2758_);
v___x_2760_ = lean_unbox(v_a_2759_);
lean_dec(v_a_2759_);
if (v___x_2760_ == 0)
{
v___y_2726_ = v_a_2704_;
v___y_2727_ = v_a_2705_;
v___y_2728_ = v_a_2706_;
v___y_2729_ = v_a_2707_;
goto v___jp_2725_;
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2761_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_2724_);
v___x_2762_ = l_Lean_MessageData_ofExpr(v_val_2724_);
v___x_2763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_2718_, v___x_2763_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_dec_ref(v___x_2764_);
v___y_2726_ = v_a_2704_;
v___y_2727_ = v_a_2705_;
v___y_2728_ = v_a_2706_;
v___y_2729_ = v_a_2707_;
goto v___jp_2725_;
}
else
{
lean_dec(v_val_2724_);
lean_dec(v_name_2717_);
lean_del_object(v___x_2714_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
return v___x_2764_;
}
}
v___jp_2725_:
{
lean_object* v___x_2730_; 
lean_inc(v_val_2724_);
v___x_2730_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2711_, v_val_2724_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2732_; lean_object* v_a_2733_; lean_object* v___x_2734_; lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2749_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref(v___x_2730_);
v___x_2732_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2724_, v___y_2727_);
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref(v___x_2732_);
v___x_2734_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2731_, v___y_2727_);
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2749_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2749_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
lean_inc(v_name_2717_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 2, v_a_2733_);
lean_ctor_set(v___x_2714_, 0, v_name_2717_);
v___x_2740_ = v___x_2714_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_name_2717_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_levelParams_2712_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_a_2733_);
v___x_2740_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2745_; 
v___x_2741_ = lean_box(0);
v___x_2742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2742_, 0, v_name_2717_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2740_);
lean_ctor_set(v___x_2743_, 1, v_a_2735_);
lean_ctor_set(v___x_2743_, 2, v___x_2742_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set_tag(v___x_2737_, 2);
lean_ctor_set(v___x_2737_, 0, v___x_2743_);
v___x_2745_ = v___x_2737_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_addDecl(v___x_2745_, v_hasTrace_2716_, v___y_2728_, v___y_2729_);
return v___x_2746_;
}
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_val_2724_);
lean_dec(v_name_2717_);
lean_del_object(v___x_2714_);
lean_dec(v_levelParams_2712_);
v_a_2750_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2730_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2730_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2767_; 
lean_dec(v_a_2720_);
lean_dec(v_name_2717_);
lean_del_object(v___x_2714_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
v___x_2765_ = lean_box(0);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2765_);
v___x_2767_ = v___x_2722_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2765_);
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
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_name_2717_);
lean_del_object(v___x_2714_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
v_a_2770_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2719_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2719_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
else
{
lean_object* v___x_2778_; lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2949_; 
v___x_2778_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_2718_, v_a_2706_);
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2949_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2949_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___f_2783_; lean_object* v___x_2784_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v_a_2788_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v_a_2801_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v_a_2808_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v_a_2819_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v_a_2835_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v_a_2840_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; uint8_t v___x_2887_; 
lean_inc(v_name_2717_);
v___f_2783_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2783_, 0, v_name_2717_);
v___x_2784_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__1));
v___x_2887_ = lean_unbox(v_a_2779_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = l_Lean_trace_profiler;
v___x_2889_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2710_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; 
lean_dec_ref(v___f_2783_);
lean_del_object(v___x_2781_);
lean_dec(v_a_2779_);
v___x_2890_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2940_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2940_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2940_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
if (lean_obj_tag(v_a_2891_) == 1)
{
lean_object* v_val_2895_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___x_2929_; lean_object* v_a_2930_; uint8_t v___x_2931_; 
lean_del_object(v___x_2893_);
v_val_2895_ = lean_ctor_get(v_a_2891_, 0);
lean_inc(v_val_2895_);
lean_dec_ref(v_a_2891_);
v___x_2929_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_2718_, v_a_2706_);
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref(v___x_2929_);
v___x_2931_ = lean_unbox(v_a_2930_);
lean_dec(v_a_2930_);
if (v___x_2931_ == 0)
{
v___y_2897_ = v_a_2704_;
v___y_2898_ = v_a_2705_;
v___y_2899_ = v_a_2706_;
v___y_2900_ = v_a_2707_;
goto v___jp_2896_;
}
else
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2932_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_2895_);
v___x_2933_ = l_Lean_MessageData_ofExpr(v_val_2895_);
v___x_2934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2932_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_2718_, v___x_2934_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_dec_ref(v___x_2935_);
v___y_2897_ = v_a_2704_;
v___y_2898_ = v_a_2705_;
v___y_2899_ = v_a_2706_;
v___y_2900_ = v_a_2707_;
goto v___jp_2896_;
}
else
{
lean_dec(v_val_2895_);
lean_dec(v_name_2717_);
lean_del_object(v___x_2714_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
return v___x_2935_;
}
}
v___jp_2896_:
{
lean_object* v___x_2901_; 
lean_inc(v_val_2895_);
v___x_2901_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue(v_name_2711_, v_val_2895_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2903_; lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2920_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref(v___x_2901_);
v___x_2903_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_2895_, v___y_2898_);
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref(v___x_2903_);
v___x_2905_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_2902_, v___y_2898_);
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_2920_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2920_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
lean_inc(v_name_2717_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 2, v_a_2904_);
lean_ctor_set(v___x_2714_, 0, v_name_2717_);
v___x_2911_ = v___x_2714_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_name_2717_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_levelParams_2712_);
lean_ctor_set(v_reuseFailAlloc_2919_, 2, v_a_2904_);
v___x_2911_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2916_; 
v___x_2912_ = lean_box(0);
v___x_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2913_, 0, v_name_2717_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2911_);
lean_ctor_set(v___x_2914_, 1, v_a_2906_);
lean_ctor_set(v___x_2914_, 2, v___x_2913_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set_tag(v___x_2908_, 2);
lean_ctor_set(v___x_2908_, 0, v___x_2914_);
v___x_2916_ = v___x_2908_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2914_);
v___x_2916_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_addDecl(v___x_2916_, v___x_2889_, v___y_2899_, v___y_2900_);
return v___x_2917_;
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec(v_val_2895_);
lean_dec(v_name_2717_);
lean_del_object(v___x_2714_);
lean_dec(v_levelParams_2712_);
v_a_2921_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2901_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2901_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2938_; 
lean_dec(v_a_2891_);
lean_dec(v_name_2717_);
lean_del_object(v___x_2714_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
v___x_2936_ = lean_box(0);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2936_);
v___x_2938_ = v___x_2893_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2936_);
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
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v_name_2717_);
lean_del_object(v___x_2714_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
v_a_2941_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2890_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2890_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
else
{
lean_del_object(v___x_2714_);
goto v___jp_2848_;
}
}
else
{
lean_del_object(v___x_2714_);
goto v___jp_2848_;
}
v___jp_2785_:
{
lean_object* v___x_2789_; double v___x_2790_; double v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; lean_object* v___x_2797_; 
v___x_2789_ = lean_io_get_num_heartbeats();
v___x_2790_ = lean_float_of_nat(v___y_2786_);
v___x_2791_ = lean_float_of_nat(v___x_2789_);
v___x_2792_ = lean_box_float(v___x_2790_);
v___x_2793_ = lean_box_float(v___x_2791_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2795_, 0, v_a_2788_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_unbox(v_a_2779_);
lean_dec(v_a_2779_);
v___x_2797_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2718_, v_hasTrace_2716_, v___x_2784_, v_options_2710_, v___x_2796_, v___y_2787_, v___f_2783_, v___x_2795_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
return v___x_2797_;
}
v___jp_2798_:
{
lean_object* v___x_2803_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v_a_2801_);
v___x_2803_ = v___x_2781_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
v___y_2786_ = v___y_2799_;
v___y_2787_ = v___y_2800_;
v_a_2788_ = v___x_2803_;
goto v___jp_2785_;
}
}
v___jp_2805_:
{
lean_object* v___x_2809_; 
v___x_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2809_, 0, v_a_2808_);
v___y_2786_ = v___y_2806_;
v___y_2787_ = v___y_2807_;
v_a_2788_ = v___x_2809_;
goto v___jp_2785_;
}
v___jp_2810_:
{
if (lean_obj_tag(v___y_2813_) == 0)
{
lean_object* v_a_2814_; 
lean_del_object(v___x_2781_);
v_a_2814_ = lean_ctor_get(v___y_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref(v___y_2813_);
v___y_2806_ = v___y_2811_;
v___y_2807_ = v___y_2812_;
v_a_2808_ = v_a_2814_;
goto v___jp_2805_;
}
else
{
lean_object* v_a_2815_; 
v_a_2815_ = lean_ctor_get(v___y_2813_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___y_2813_);
v___y_2799_ = v___y_2811_;
v___y_2800_ = v___y_2812_;
v_a_2801_ = v_a_2815_;
goto v___jp_2798_;
}
}
v___jp_2816_:
{
lean_object* v___x_2820_; double v___x_2821_; double v___x_2822_; double v___x_2823_; double v___x_2824_; double v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; lean_object* v___x_2831_; 
v___x_2820_ = lean_io_mono_nanos_now();
v___x_2821_ = lean_float_of_nat(v___y_2818_);
v___x_2822_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_2823_ = lean_float_div(v___x_2821_, v___x_2822_);
v___x_2824_ = lean_float_of_nat(v___x_2820_);
v___x_2825_ = lean_float_div(v___x_2824_, v___x_2822_);
v___x_2826_ = lean_box_float(v___x_2823_);
v___x_2827_ = lean_box_float(v___x_2825_);
v___x_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v_a_2819_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_unbox(v_a_2779_);
lean_dec(v_a_2779_);
v___x_2831_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_2718_, v_hasTrace_2716_, v___x_2784_, v_options_2710_, v___x_2830_, v___y_2817_, v___f_2783_, v___x_2829_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
return v___x_2831_;
}
v___jp_2832_:
{
lean_object* v___x_2836_; 
v___x_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2836_, 0, v_a_2835_);
v___y_2817_ = v___y_2833_;
v___y_2818_ = v___y_2834_;
v_a_2819_ = v___x_2836_;
goto v___jp_2816_;
}
v___jp_2837_:
{
lean_object* v___x_2841_; 
v___x_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2841_, 0, v_a_2840_);
v___y_2817_ = v___y_2838_;
v___y_2818_ = v___y_2839_;
v_a_2819_ = v___x_2841_;
goto v___jp_2816_;
}
v___jp_2842_:
{
if (lean_obj_tag(v___y_2845_) == 0)
{
lean_object* v_a_2846_; 
v_a_2846_ = lean_ctor_get(v___y_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref(v___y_2845_);
v___y_2833_ = v___y_2843_;
v___y_2834_ = v___y_2844_;
v_a_2835_ = v_a_2846_;
goto v___jp_2832_;
}
else
{
lean_object* v_a_2847_; 
v_a_2847_ = lean_ctor_get(v___y_2845_, 0);
lean_inc(v_a_2847_);
lean_dec_ref(v___y_2845_);
v___y_2838_ = v___y_2843_;
v___y_2839_ = v___y_2844_;
v_a_2840_ = v_a_2847_;
goto v___jp_2837_;
}
}
v___jp_2848_:
{
lean_object* v___x_2849_; lean_object* v_a_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2849_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_2707_);
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2849_);
v___x_2851_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2852_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_2710_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_del_object(v___x_2781_);
v___x_2853_ = lean_io_mono_nanos_now();
v___x_2854_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref(v___x_2854_);
if (lean_obj_tag(v_a_2855_) == 1)
{
lean_object* v_val_2856_; lean_object* v___x_2857_; lean_object* v_a_2858_; uint8_t v___x_2859_; 
v_val_2856_ = lean_ctor_get(v_a_2855_, 0);
lean_inc(v_val_2856_);
lean_dec_ref(v_a_2855_);
v___x_2857_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_2718_, v_a_2706_);
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___x_2857_);
v___x_2859_ = lean_unbox(v_a_2858_);
lean_dec(v_a_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_box(0);
v___x_2861_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2711_, v_val_2856_, v_name_2717_, v_levelParams_2712_, v___x_2852_, v___x_2860_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
v___y_2843_ = v_a_2850_;
v___y_2844_ = v___x_2853_;
v___y_2845_ = v___x_2861_;
goto v___jp_2842_;
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2862_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_2856_);
v___x_2863_ = l_Lean_MessageData_ofExpr(v_val_2856_);
v___x_2864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_2718_, v___x_2864_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2867_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref(v___x_2865_);
v___x_2867_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__1(v_name_2711_, v_val_2856_, v_name_2717_, v_levelParams_2712_, v___x_2852_, v_a_2866_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
v___y_2843_ = v_a_2850_;
v___y_2844_ = v___x_2853_;
v___y_2845_ = v___x_2867_;
goto v___jp_2842_;
}
else
{
lean_dec(v_val_2856_);
lean_dec(v_name_2717_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
v___y_2843_ = v_a_2850_;
v___y_2844_ = v___x_2853_;
v___y_2845_ = v___x_2865_;
goto v___jp_2842_;
}
}
}
else
{
lean_object* v___x_2868_; 
lean_dec(v_a_2855_);
lean_dec(v_name_2717_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
v___x_2868_ = lean_box(0);
v___y_2833_ = v_a_2850_;
v___y_2834_ = v___x_2853_;
v_a_2835_ = v___x_2868_;
goto v___jp_2832_;
}
}
else
{
lean_object* v_a_2869_; 
lean_dec(v_name_2717_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
v_a_2869_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2869_);
lean_dec_ref(v___x_2854_);
v___y_2838_ = v_a_2850_;
v___y_2839_ = v___x_2853_;
v_a_2840_ = v_a_2869_;
goto v___jp_2837_;
}
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = lean_io_get_num_heartbeats();
v___x_2871_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremType_x3f(v_ctorVal_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref(v___x_2871_);
if (lean_obj_tag(v_a_2872_) == 1)
{
lean_object* v_val_2873_; lean_object* v___x_2874_; lean_object* v_a_2875_; uint8_t v___x_2876_; 
v_val_2873_ = lean_ctor_get(v_a_2872_, 0);
lean_inc(v_val_2873_);
lean_dec_ref(v_a_2872_);
v___x_2874_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_2718_, v_a_2706_);
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref(v___x_2874_);
v___x_2876_ = lean_unbox(v_a_2875_);
lean_dec(v_a_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = lean_box(0);
v___x_2878_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2711_, v_val_2873_, v_name_2717_, v_levelParams_2712_, v___x_2877_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
v___y_2811_ = v___x_2870_;
v___y_2812_ = v_a_2850_;
v___y_2813_ = v___x_2878_;
goto v___jp_2810_;
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2879_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_2873_);
v___x_2880_ = l_Lean_MessageData_ofExpr(v_val_2873_);
v___x_2881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_2718_, v___x_2881_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2882_);
v___x_2884_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__2(v_name_2711_, v_val_2873_, v_name_2717_, v_levelParams_2712_, v_a_2883_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
v___y_2811_ = v___x_2870_;
v___y_2812_ = v_a_2850_;
v___y_2813_ = v___x_2884_;
goto v___jp_2810_;
}
else
{
lean_dec(v_val_2873_);
lean_dec(v_name_2717_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
v___y_2811_ = v___x_2870_;
v___y_2812_ = v_a_2850_;
v___y_2813_ = v___x_2882_;
goto v___jp_2810_;
}
}
}
else
{
lean_object* v___x_2885_; 
lean_dec(v_a_2872_);
lean_del_object(v___x_2781_);
lean_dec(v_name_2717_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
v___x_2885_ = lean_box(0);
v___y_2806_ = v___x_2870_;
v___y_2807_ = v_a_2850_;
v_a_2808_ = v___x_2885_;
goto v___jp_2805_;
}
}
else
{
lean_object* v_a_2886_; 
lean_dec(v_name_2717_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
v_a_2886_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2886_);
lean_dec_ref(v___x_2871_);
v___y_2799_ = v___x_2870_;
v___y_2800_ = v_a_2850_;
v_a_2801_ = v_a_2886_;
goto v___jp_2798_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___boxed(lean_object* v_ctorVal_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_ctorVal_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(lean_object* v_00_u03b1_2959_, lean_object* v_x_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___redArg(v_x_2960_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2967_, lean_object* v_x_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3_spec__5(v_00_u03b1_2967_, v_x_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveEqTheoremNameFor(lean_object* v_ctorName_2978_){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = ((lean_object*)(l_Lean_Meta_mkInjectiveEqTheoremNameFor___closed__1));
v___x_2980_ = l_Lean_Name_append(v_ctorName_2978_, v___x_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(lean_object* v_ctorVal_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
uint8_t v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = 1;
v___x_2988_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f(v_ctorVal_2981_, v___x_2987_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f___boxed(lean_object* v_ctorVal_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(lean_object* v_e_2996_, lean_object* v_t_2997_, lean_object* v_acc_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_t_2997_, v_a_2999_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3025_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3004_ = v___x_3001_;
v_isShared_3005_ = v_isSharedCheck_3025_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_3001_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3025_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3011_ = l_Lean_Expr_cleanupAnnotations(v_a_3002_);
v___x_3012_ = l_Lean_Expr_isApp(v___x_3011_);
if (v___x_3012_ == 0)
{
lean_dec_ref(v___x_3011_);
goto v___jp_3006_;
}
else
{
lean_object* v_arg_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v_arg_3013_ = lean_ctor_get(v___x_3011_, 1);
lean_inc_ref(v_arg_3013_);
v___x_3014_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3011_);
v___x_3015_ = l_Lean_Expr_isApp(v___x_3014_);
if (v___x_3015_ == 0)
{
lean_dec_ref(v___x_3014_);
lean_dec_ref(v_arg_3013_);
goto v___jp_3006_;
}
else
{
lean_object* v_arg_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v_arg_3016_ = lean_ctor_get(v___x_3014_, 1);
lean_inc_ref(v_arg_3016_);
v___x_3017_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3014_);
v___x_3018_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3019_ = l_Lean_Expr_isConstOf(v___x_3017_, v___x_3018_);
lean_dec_ref(v___x_3017_);
if (v___x_3019_ == 0)
{
lean_dec_ref(v_arg_3016_);
lean_dec_ref(v_arg_3013_);
goto v___jp_3006_;
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
lean_del_object(v___x_3004_);
v___x_3020_ = lean_unsigned_to_nat(0u);
v___x_3021_ = l_Lean_mkProj(v___x_3018_, v___x_3020_, v_e_2996_);
lean_inc_ref(v___x_3021_);
v___x_3022_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v___x_3021_, v_arg_3016_, v_acc_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref(v___x_3022_);
v_e_2996_ = v___x_3021_;
v_t_2997_ = v_arg_3013_;
v_acc_2998_ = v_a_3023_;
goto _start;
}
else
{
lean_dec_ref(v___x_3021_);
lean_dec_ref(v_arg_3013_);
return v___x_3022_;
}
}
}
}
v___jp_3006_:
{
lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3007_ = lean_array_push(v_acc_2998_, v_e_2996_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3007_);
v___x_3009_ = v___x_3004_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref(v_acc_2998_);
lean_dec_ref(v_e_2996_);
v_a_3026_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3001_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3001_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg___boxed(lean_object* v_e_3034_, lean_object* v_t_3035_, lean_object* v_acc_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3034_, v_t_3035_, v_acc_3036_, v_a_3037_);
lean_dec(v_a_3037_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(lean_object* v_e_3040_, lean_object* v_t_3041_, lean_object* v_acc_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3040_, v_t_3041_, v_acc_3042_, v_a_3044_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___boxed(lean_object* v_e_3049_, lean_object* v_t_3050_, lean_object* v_acc_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go(v_e_3049_, v_t_3050_, v_acc_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(lean_object* v_e_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v___x_3064_; 
lean_inc(v_a_3062_);
lean_inc_ref(v_a_3061_);
lean_inc(v_a_3060_);
lean_inc_ref(v_a_3059_);
lean_inc_ref(v_e_3058_);
v___x_3064_ = lean_infer_type(v_e_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref(v___x_3064_);
v___x_3066_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_3067_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections_go___redArg(v_e_3058_, v_a_3065_, v___x_3066_, v_a_3060_);
return v___x_3067_;
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v_e_3058_);
v_a_3068_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3064_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3064_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections___boxed(lean_object* v_e_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l___private_Lean_Meta_Injective_0__Lean_Meta_andProjections(v_e_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
lean_dec(v_a_3080_);
lean_dec_ref(v_a_3079_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
return v_res_3082_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = lean_box(0);
v___x_3089_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__2));
v___x_3090_ = l_Lean_mkConst(v___x_3089_, v___x_3088_);
return v___x_3090_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__4));
v___x_3093_ = l_Lean_stringToMessageData(v___x_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(lean_object* v_b_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___x_3100_; 
lean_inc(v_b_3094_);
v___x_3100_ = l_Lean_MVarId_getType(v_b_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3181_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3181_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3181_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
if (lean_obj_tag(v_a_3101_) == 7)
{
lean_object* v_binderType_3105_; lean_object* v_body_3106_; uint8_t v___x_3107_; lean_object* v_mvarId_u2082_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; 
v_binderType_3105_ = lean_ctor_get(v_a_3101_, 1);
lean_inc_ref(v_binderType_3105_);
v_body_3106_ = lean_ctor_get(v_a_3101_, 2);
lean_inc_ref(v_body_3106_);
lean_dec_ref(v_a_3101_);
v___x_3107_ = l_Lean_Expr_hasLooseBVars(v_body_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3126_; 
lean_del_object(v___x_3103_);
v___x_3126_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3105_, v___y_3096_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3126_);
v___x_3128_ = l_Lean_Expr_cleanupAnnotations(v_a_3127_);
v___x_3129_ = l_Lean_Expr_isApp(v___x_3128_);
if (v___x_3129_ == 0)
{
lean_dec_ref(v___x_3128_);
lean_dec_ref(v_body_3106_);
v_mvarId_u2082_3109_ = v_b_3094_;
v___y_3110_ = v___y_3095_;
v___y_3111_ = v___y_3096_;
v___y_3112_ = v___y_3097_;
v___y_3113_ = v___y_3098_;
goto v___jp_3108_;
}
else
{
lean_object* v_arg_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; 
v_arg_3130_ = lean_ctor_get(v___x_3128_, 1);
lean_inc_ref(v_arg_3130_);
v___x_3131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3128_);
v___x_3132_ = l_Lean_Expr_isApp(v___x_3131_);
if (v___x_3132_ == 0)
{
lean_dec_ref(v___x_3131_);
lean_dec_ref(v_arg_3130_);
lean_dec_ref(v_body_3106_);
v_mvarId_u2082_3109_ = v_b_3094_;
v___y_3110_ = v___y_3095_;
v___y_3111_ = v___y_3096_;
v___y_3112_ = v___y_3097_;
v___y_3113_ = v___y_3098_;
goto v___jp_3108_;
}
else
{
lean_object* v_arg_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v_arg_3133_ = lean_ctor_get(v___x_3131_, 1);
lean_inc_ref(v_arg_3133_);
v___x_3134_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3131_);
v___x_3135_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f_spec__0___redArg___closed__1));
v___x_3136_ = l_Lean_Expr_isConstOf(v___x_3134_, v___x_3135_);
lean_dec_ref(v___x_3134_);
if (v___x_3136_ == 0)
{
lean_dec_ref(v_arg_3133_);
lean_dec_ref(v_arg_3130_);
lean_dec_ref(v_body_3106_);
v_mvarId_u2082_3109_ = v_b_3094_;
v___y_3110_ = v___y_3095_;
v___y_3111_ = v___y_3096_;
v___y_3112_ = v___y_3097_;
v___y_3113_ = v___y_3098_;
goto v___jp_3108_;
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3137_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__3);
v___x_3138_ = l_Lean_mkApp3(v___x_3137_, v_arg_3133_, v_arg_3130_, v_body_3106_);
v___x_3139_ = lean_unsigned_to_nat(1u);
lean_inc(v_b_3094_);
v___x_3140_ = l_Lean_MVarId_applyN(v_b_3094_, v___x_3138_, v___x_3139_, v___x_3136_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref(v___x_3140_);
if (lean_obj_tag(v_a_3141_) == 1)
{
lean_object* v_tail_3157_; 
v_tail_3157_ = lean_ctor_get(v_a_3141_, 1);
if (lean_obj_tag(v_tail_3157_) == 0)
{
lean_object* v_head_3158_; 
lean_dec(v_b_3094_);
v_head_3158_ = lean_ctor_get(v_a_3141_, 0);
lean_inc(v_head_3158_);
lean_dec_ref(v_a_3141_);
v_mvarId_u2082_3109_ = v_head_3158_;
v___y_3110_ = v___y_3095_;
v___y_3111_ = v___y_3096_;
v___y_3112_ = v___y_3097_;
v___y_3113_ = v___y_3098_;
goto v___jp_3108_;
}
else
{
lean_dec_ref(v_a_3141_);
v___y_3143_ = v___y_3095_;
v___y_3144_ = v___y_3096_;
v___y_3145_ = v___y_3097_;
v___y_3146_ = v___y_3098_;
goto v___jp_3142_;
}
}
else
{
lean_dec(v_a_3141_);
v___y_3143_ = v___y_3095_;
v___y_3144_ = v___y_3096_;
v___y_3145_ = v___y_3097_;
v___y_3146_ = v___y_3098_;
goto v___jp_3142_;
}
v___jp_3142_:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___closed__5);
v___x_3148_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3147_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_dec_ref(v___x_3148_);
v_mvarId_u2082_3109_ = v_b_3094_;
v___y_3110_ = v___y_3143_;
v___y_3111_ = v___y_3144_;
v___y_3112_ = v___y_3145_;
v___y_3113_ = v___y_3146_;
goto v___jp_3108_;
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec(v_b_3094_);
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3148_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3148_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec(v_b_3094_);
v_a_3159_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3140_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3140_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec_ref(v_body_3106_);
lean_dec(v_b_3094_);
v_a_3167_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3126_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3126_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
else
{
lean_object* v___x_3176_; 
lean_dec_ref(v_body_3106_);
lean_dec_ref(v_binderType_3105_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v_b_3094_);
v___x_3176_ = v___x_3103_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_b_3094_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
v___jp_3108_:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Lean_Meta_introSubstEq(v_mvarId_u2082_3109_, v___x_3107_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v_snd_3116_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref(v___x_3114_);
v_snd_3116_ = lean_ctor_get(v_a_3115_, 1);
lean_inc(v_snd_3116_);
lean_dec(v_a_3115_);
v_b_3094_ = v_snd_3116_;
goto _start;
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
v_a_3118_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3114_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3114_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
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
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
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
lean_object* v___x_3179_; 
lean_dec(v_a_3101_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v_b_3094_);
v___x_3179_ = v___x_3103_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_b_3094_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v_b_3094_);
v_a_3182_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3100_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3100_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1___boxed(lean_object* v_b_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_b_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_x_3197_, lean_object* v_x_3198_, lean_object* v_x_3199_, lean_object* v_x_3200_){
_start:
{
lean_object* v_ks_3201_; lean_object* v_vs_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3226_; 
v_ks_3201_ = lean_ctor_get(v_x_3197_, 0);
v_vs_3202_ = lean_ctor_get(v_x_3197_, 1);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_x_3197_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3204_ = v_x_3197_;
v_isShared_3205_ = v_isSharedCheck_3226_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_vs_3202_);
lean_inc(v_ks_3201_);
lean_dec(v_x_3197_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3226_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; uint8_t v___x_3207_; 
v___x_3206_ = lean_array_get_size(v_ks_3201_);
v___x_3207_ = lean_nat_dec_lt(v_x_3198_, v___x_3206_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3211_; 
lean_dec(v_x_3198_);
v___x_3208_ = lean_array_push(v_ks_3201_, v_x_3199_);
v___x_3209_ = lean_array_push(v_vs_3202_, v_x_3200_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v___x_3209_);
lean_ctor_set(v___x_3204_, 0, v___x_3208_);
v___x_3211_ = v___x_3204_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3208_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v___x_3209_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
else
{
lean_object* v_k_x27_3213_; uint8_t v___x_3214_; 
v_k_x27_3213_ = lean_array_fget_borrowed(v_ks_3201_, v_x_3198_);
v___x_3214_ = l_Lean_instBEqMVarId_beq(v_x_3199_, v_k_x27_3213_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3216_; 
if (v_isShared_3205_ == 0)
{
v___x_3216_ = v___x_3204_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_ks_3201_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_vs_3202_);
v___x_3216_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = lean_unsigned_to_nat(1u);
v___x_3218_ = lean_nat_add(v_x_3198_, v___x_3217_);
lean_dec(v_x_3198_);
v_x_3197_ = v___x_3216_;
v_x_3198_ = v___x_3218_;
goto _start;
}
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3221_ = lean_array_fset(v_ks_3201_, v_x_3198_, v_x_3199_);
v___x_3222_ = lean_array_fset(v_vs_3202_, v_x_3198_, v_x_3200_);
lean_dec(v_x_3198_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v___x_3222_);
lean_ctor_set(v___x_3204_, 0, v___x_3221_);
v___x_3224_ = v___x_3204_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_3227_, lean_object* v_k_3228_, lean_object* v_v_3229_){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = lean_unsigned_to_nat(0u);
v___x_3231_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_n_3227_, v___x_3230_, v_k_3228_, v_v_3229_);
return v___x_3231_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_3232_; size_t v___x_3233_; size_t v___x_3234_; 
v___x_3232_ = ((size_t)5ULL);
v___x_3233_ = ((size_t)1ULL);
v___x_3234_ = lean_usize_shift_left(v___x_3233_, v___x_3232_);
return v___x_3234_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_3235_; size_t v___x_3236_; size_t v___x_3237_; 
v___x_3235_ = ((size_t)1ULL);
v___x_3236_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_3237_ = lean_usize_sub(v___x_3236_, v___x_3235_);
return v___x_3237_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3239_, size_t v_x_3240_, size_t v_x_3241_, lean_object* v_x_3242_, lean_object* v_x_3243_){
_start:
{
if (lean_obj_tag(v_x_3239_) == 0)
{
lean_object* v_es_3244_; size_t v___x_3245_; size_t v___x_3246_; size_t v___x_3247_; size_t v___x_3248_; lean_object* v_j_3249_; lean_object* v___x_3250_; uint8_t v___x_3251_; 
v_es_3244_ = lean_ctor_get(v_x_3239_, 0);
v___x_3245_ = ((size_t)5ULL);
v___x_3246_ = ((size_t)1ULL);
v___x_3247_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_3248_ = lean_usize_land(v_x_3240_, v___x_3247_);
v_j_3249_ = lean_usize_to_nat(v___x_3248_);
v___x_3250_ = lean_array_get_size(v_es_3244_);
v___x_3251_ = lean_nat_dec_lt(v_j_3249_, v___x_3250_);
if (v___x_3251_ == 0)
{
lean_dec(v_j_3249_);
lean_dec(v_x_3243_);
lean_dec(v_x_3242_);
return v_x_3239_;
}
else
{
lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3288_; 
lean_inc_ref(v_es_3244_);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_x_3239_);
if (v_isSharedCheck_3288_ == 0)
{
lean_object* v_unused_3289_; 
v_unused_3289_ = lean_ctor_get(v_x_3239_, 0);
lean_dec(v_unused_3289_);
v___x_3253_ = v_x_3239_;
v_isShared_3254_ = v_isSharedCheck_3288_;
goto v_resetjp_3252_;
}
else
{
lean_dec(v_x_3239_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3288_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v_v_3255_; lean_object* v___x_3256_; lean_object* v_xs_x27_3257_; lean_object* v___y_3259_; 
v_v_3255_ = lean_array_fget(v_es_3244_, v_j_3249_);
v___x_3256_ = lean_box(0);
v_xs_x27_3257_ = lean_array_fset(v_es_3244_, v_j_3249_, v___x_3256_);
switch(lean_obj_tag(v_v_3255_))
{
case 0:
{
lean_object* v_key_3264_; lean_object* v_val_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3275_; 
v_key_3264_ = lean_ctor_get(v_v_3255_, 0);
v_val_3265_ = lean_ctor_get(v_v_3255_, 1);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_v_3255_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3267_ = v_v_3255_;
v_isShared_3268_ = v_isSharedCheck_3275_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_val_3265_);
lean_inc(v_key_3264_);
lean_dec(v_v_3255_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3275_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
uint8_t v___x_3269_; 
v___x_3269_ = l_Lean_instBEqMVarId_beq(v_x_3242_, v_key_3264_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_del_object(v___x_3267_);
v___x_3270_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3264_, v_val_3265_, v_x_3242_, v_x_3243_);
v___x_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3270_);
v___y_3259_ = v___x_3271_;
goto v___jp_3258_;
}
else
{
lean_object* v___x_3273_; 
lean_dec(v_val_3265_);
lean_dec(v_key_3264_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 1, v_x_3243_);
lean_ctor_set(v___x_3267_, 0, v_x_3242_);
v___x_3273_ = v___x_3267_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_x_3242_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_x_3243_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
v___y_3259_ = v___x_3273_;
goto v___jp_3258_;
}
}
}
}
case 1:
{
lean_object* v_node_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3286_; 
v_node_3276_ = lean_ctor_get(v_v_3255_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v_v_3255_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3278_ = v_v_3255_;
v_isShared_3279_ = v_isSharedCheck_3286_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_node_3276_);
lean_dec(v_v_3255_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3286_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
size_t v___x_3280_; size_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3280_ = lean_usize_shift_right(v_x_3240_, v___x_3245_);
v___x_3281_ = lean_usize_add(v_x_3241_, v___x_3246_);
v___x_3282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_node_3276_, v___x_3280_, v___x_3281_, v_x_3242_, v_x_3243_);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3282_);
v___x_3284_ = v___x_3278_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3282_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
v___y_3259_ = v___x_3284_;
goto v___jp_3258_;
}
}
}
default: 
{
lean_object* v___x_3287_; 
v___x_3287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3287_, 0, v_x_3242_);
lean_ctor_set(v___x_3287_, 1, v_x_3243_);
v___y_3259_ = v___x_3287_;
goto v___jp_3258_;
}
}
v___jp_3258_:
{
lean_object* v___x_3260_; lean_object* v___x_3262_; 
v___x_3260_ = lean_array_fset(v_xs_x27_3257_, v_j_3249_, v___y_3259_);
lean_dec(v_j_3249_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3260_);
v___x_3262_ = v___x_3253_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
else
{
lean_object* v_ks_3290_; lean_object* v_vs_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3311_; 
v_ks_3290_ = lean_ctor_get(v_x_3239_, 0);
v_vs_3291_ = lean_ctor_get(v_x_3239_, 1);
v_isSharedCheck_3311_ = !lean_is_exclusive(v_x_3239_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3293_ = v_x_3239_;
v_isShared_3294_ = v_isSharedCheck_3311_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_vs_3291_);
lean_inc(v_ks_3290_);
lean_dec(v_x_3239_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3311_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_ks_3290_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_vs_3291_);
v___x_3296_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v_newNode_3297_; uint8_t v___y_3299_; size_t v___x_3305_; uint8_t v___x_3306_; 
v_newNode_3297_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v___x_3296_, v_x_3242_, v_x_3243_);
v___x_3305_ = ((size_t)7ULL);
v___x_3306_ = lean_usize_dec_le(v___x_3305_, v_x_3241_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3307_; lean_object* v___x_3308_; uint8_t v___x_3309_; 
v___x_3307_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3297_);
v___x_3308_ = lean_unsigned_to_nat(4u);
v___x_3309_ = lean_nat_dec_lt(v___x_3307_, v___x_3308_);
lean_dec(v___x_3307_);
v___y_3299_ = v___x_3309_;
goto v___jp_3298_;
}
else
{
v___y_3299_ = v___x_3306_;
goto v___jp_3298_;
}
v___jp_3298_:
{
if (v___y_3299_ == 0)
{
lean_object* v_ks_3300_; lean_object* v_vs_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_ks_3300_ = lean_ctor_get(v_newNode_3297_, 0);
lean_inc_ref(v_ks_3300_);
v_vs_3301_ = lean_ctor_get(v_newNode_3297_, 1);
lean_inc_ref(v_vs_3301_);
lean_dec_ref(v_newNode_3297_);
v___x_3302_ = lean_unsigned_to_nat(0u);
v___x_3303_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_3304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_x_3241_, v_ks_3300_, v_vs_3301_, v___x_3302_, v___x_3303_);
lean_dec_ref(v_vs_3301_);
lean_dec_ref(v_ks_3300_);
return v___x_3304_;
}
else
{
return v_newNode_3297_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_3312_, lean_object* v_keys_3313_, lean_object* v_vals_3314_, lean_object* v_i_3315_, lean_object* v_entries_3316_){
_start:
{
lean_object* v___x_3317_; uint8_t v___x_3318_; 
v___x_3317_ = lean_array_get_size(v_keys_3313_);
v___x_3318_ = lean_nat_dec_lt(v_i_3315_, v___x_3317_);
if (v___x_3318_ == 0)
{
lean_dec(v_i_3315_);
return v_entries_3316_;
}
else
{
lean_object* v_k_3319_; lean_object* v_v_3320_; uint64_t v___x_3321_; size_t v_h_3322_; size_t v___x_3323_; lean_object* v___x_3324_; size_t v___x_3325_; size_t v___x_3326_; size_t v___x_3327_; size_t v_h_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_k_3319_ = lean_array_fget_borrowed(v_keys_3313_, v_i_3315_);
v_v_3320_ = lean_array_fget_borrowed(v_vals_3314_, v_i_3315_);
v___x_3321_ = l_Lean_instHashableMVarId_hash(v_k_3319_);
v_h_3322_ = lean_uint64_to_usize(v___x_3321_);
v___x_3323_ = ((size_t)5ULL);
v___x_3324_ = lean_unsigned_to_nat(1u);
v___x_3325_ = ((size_t)1ULL);
v___x_3326_ = lean_usize_sub(v_depth_3312_, v___x_3325_);
v___x_3327_ = lean_usize_mul(v___x_3323_, v___x_3326_);
v_h_3328_ = lean_usize_shift_right(v_h_3322_, v___x_3327_);
v___x_3329_ = lean_nat_add(v_i_3315_, v___x_3324_);
lean_dec(v_i_3315_);
lean_inc(v_v_3320_);
lean_inc(v_k_3319_);
v___x_3330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_entries_3316_, v_h_3328_, v_depth_3312_, v_k_3319_, v_v_3320_);
v_i_3315_ = v___x_3329_;
v_entries_3316_ = v___x_3330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_3332_, lean_object* v_keys_3333_, lean_object* v_vals_3334_, lean_object* v_i_3335_, lean_object* v_entries_3336_){
_start:
{
size_t v_depth_boxed_3337_; lean_object* v_res_3338_; 
v_depth_boxed_3337_ = lean_unbox_usize(v_depth_3332_);
lean_dec(v_depth_3332_);
v_res_3338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_3337_, v_keys_3333_, v_vals_3334_, v_i_3335_, v_entries_3336_);
lean_dec_ref(v_vals_3334_);
lean_dec_ref(v_keys_3333_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3339_, lean_object* v_x_3340_, lean_object* v_x_3341_, lean_object* v_x_3342_, lean_object* v_x_3343_){
_start:
{
size_t v_x_5080__boxed_3344_; size_t v_x_5081__boxed_3345_; lean_object* v_res_3346_; 
v_x_5080__boxed_3344_ = lean_unbox_usize(v_x_3340_);
lean_dec(v_x_3340_);
v_x_5081__boxed_3345_ = lean_unbox_usize(v_x_3341_);
lean_dec(v_x_3341_);
v_res_3346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3339_, v_x_5080__boxed_3344_, v_x_5081__boxed_3345_, v_x_3342_, v_x_3343_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(lean_object* v_x_3347_, lean_object* v_x_3348_, lean_object* v_x_3349_){
_start:
{
uint64_t v___x_3350_; size_t v___x_3351_; size_t v___x_3352_; lean_object* v___x_3353_; 
v___x_3350_ = l_Lean_instHashableMVarId_hash(v_x_3348_);
v___x_3351_ = lean_uint64_to_usize(v___x_3350_);
v___x_3352_ = ((size_t)1ULL);
v___x_3353_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3347_, v___x_3351_, v___x_3352_, v_x_3348_, v_x_3349_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(lean_object* v_mvarId_3354_, lean_object* v_val_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v___x_3358_; lean_object* v_mctx_3359_; lean_object* v_cache_3360_; lean_object* v_zetaDeltaFVarIds_3361_; lean_object* v_postponed_3362_; lean_object* v_diag_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3390_; 
v___x_3358_ = lean_st_ref_take(v___y_3356_);
v_mctx_3359_ = lean_ctor_get(v___x_3358_, 0);
v_cache_3360_ = lean_ctor_get(v___x_3358_, 1);
v_zetaDeltaFVarIds_3361_ = lean_ctor_get(v___x_3358_, 2);
v_postponed_3362_ = lean_ctor_get(v___x_3358_, 3);
v_diag_3363_ = lean_ctor_get(v___x_3358_, 4);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3365_ = v___x_3358_;
v_isShared_3366_ = v_isSharedCheck_3390_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_diag_3363_);
lean_inc(v_postponed_3362_);
lean_inc(v_zetaDeltaFVarIds_3361_);
lean_inc(v_cache_3360_);
lean_inc(v_mctx_3359_);
lean_dec(v___x_3358_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3390_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v_depth_3367_; lean_object* v_levelAssignDepth_3368_; lean_object* v_mvarCounter_3369_; lean_object* v_lDepth_3370_; lean_object* v_decls_3371_; lean_object* v_userNames_3372_; lean_object* v_lAssignment_3373_; lean_object* v_eAssignment_3374_; lean_object* v_dAssignment_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3389_; 
v_depth_3367_ = lean_ctor_get(v_mctx_3359_, 0);
v_levelAssignDepth_3368_ = lean_ctor_get(v_mctx_3359_, 1);
v_mvarCounter_3369_ = lean_ctor_get(v_mctx_3359_, 2);
v_lDepth_3370_ = lean_ctor_get(v_mctx_3359_, 3);
v_decls_3371_ = lean_ctor_get(v_mctx_3359_, 4);
v_userNames_3372_ = lean_ctor_get(v_mctx_3359_, 5);
v_lAssignment_3373_ = lean_ctor_get(v_mctx_3359_, 6);
v_eAssignment_3374_ = lean_ctor_get(v_mctx_3359_, 7);
v_dAssignment_3375_ = lean_ctor_get(v_mctx_3359_, 8);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_mctx_3359_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3377_ = v_mctx_3359_;
v_isShared_3378_ = v_isSharedCheck_3389_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_dAssignment_3375_);
lean_inc(v_eAssignment_3374_);
lean_inc(v_lAssignment_3373_);
lean_inc(v_userNames_3372_);
lean_inc(v_decls_3371_);
lean_inc(v_lDepth_3370_);
lean_inc(v_mvarCounter_3369_);
lean_inc(v_levelAssignDepth_3368_);
lean_inc(v_depth_3367_);
lean_dec(v_mctx_3359_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3389_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3379_; lean_object* v___x_3381_; 
v___x_3379_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_eAssignment_3374_, v_mvarId_3354_, v_val_3355_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 7, v___x_3379_);
v___x_3381_ = v___x_3377_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_depth_3367_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_levelAssignDepth_3368_);
lean_ctor_set(v_reuseFailAlloc_3388_, 2, v_mvarCounter_3369_);
lean_ctor_set(v_reuseFailAlloc_3388_, 3, v_lDepth_3370_);
lean_ctor_set(v_reuseFailAlloc_3388_, 4, v_decls_3371_);
lean_ctor_set(v_reuseFailAlloc_3388_, 5, v_userNames_3372_);
lean_ctor_set(v_reuseFailAlloc_3388_, 6, v_lAssignment_3373_);
lean_ctor_set(v_reuseFailAlloc_3388_, 7, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3388_, 8, v_dAssignment_3375_);
v___x_3381_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v___x_3383_; 
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3381_);
v___x_3383_ = v___x_3365_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_cache_3360_);
lean_ctor_set(v_reuseFailAlloc_3387_, 2, v_zetaDeltaFVarIds_3361_);
lean_ctor_set(v_reuseFailAlloc_3387_, 3, v_postponed_3362_);
lean_ctor_set(v_reuseFailAlloc_3387_, 4, v_diag_3363_);
v___x_3383_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3384_ = lean_st_ref_set(v___y_3356_, v___x_3383_);
v___x_3385_ = lean_box(0);
v___x_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
return v___x_3386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg___boxed(lean_object* v_mvarId_3391_, lean_object* v_val_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3391_, v_val_3392_, v___y_3393_);
lean_dec(v___y_3393_);
return v_res_3395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = lean_box(0);
v___x_3402_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_3403_ = l_Lean_mkConst(v___x_3402_, v___x_3401_);
return v___x_3403_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__5));
v___x_3410_ = l_Lean_stringToMessageData(v___x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(lean_object* v_ctorVal_3411_, lean_object* v_xs_3412_, lean_object* v_type_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = lean_box(0);
v___x_3420_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_3413_, v___x_3419_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; uint8_t v___x_3426_; lean_object* v___y_3428_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref(v___x_3420_);
v___x_3422_ = l_Lean_Expr_mvarId_x21(v_a_3421_);
v___x_3423_ = lean_box(0);
v___x_3424_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__3);
v___x_3425_ = 1;
v___x_3426_ = 0;
v___x_3439_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__4));
v___x_3440_ = lean_box(0);
v___x_3441_ = l_Lean_MVarId_apply(v___x_3422_, v___x_3424_, v___x_3439_, v___x_3440_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref(v___x_3441_);
if (lean_obj_tag(v_a_3442_) == 1)
{
lean_object* v_tail_3456_; 
v_tail_3456_ = lean_ctor_get(v_a_3442_, 1);
lean_inc(v_tail_3456_);
if (lean_obj_tag(v_tail_3456_) == 1)
{
lean_object* v_tail_3457_; 
v_tail_3457_ = lean_ctor_get(v_tail_3456_, 1);
if (lean_obj_tag(v_tail_3457_) == 0)
{
lean_object* v_toConstantVal_3458_; lean_object* v_head_3459_; lean_object* v_head_3460_; lean_object* v_name_3461_; lean_object* v_levelParams_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v_toConstantVal_3458_ = lean_ctor_get(v_ctorVal_3411_, 0);
lean_inc_ref(v_toConstantVal_3458_);
lean_dec_ref(v_ctorVal_3411_);
v_head_3459_ = lean_ctor_get(v_a_3442_, 0);
lean_inc(v_head_3459_);
lean_dec_ref(v_a_3442_);
v_head_3460_ = lean_ctor_get(v_tail_3456_, 0);
lean_inc(v_head_3460_);
lean_dec_ref(v_tail_3456_);
v_name_3461_ = lean_ctor_get(v_toConstantVal_3458_, 0);
lean_inc(v_name_3461_);
v_levelParams_3462_ = lean_ctor_get(v_toConstantVal_3458_, 1);
lean_inc(v_levelParams_3462_);
lean_dec_ref(v_toConstantVal_3458_);
lean_inc(v_name_3461_);
v___x_3463_ = l_Lean_Meta_mkInjectiveTheoremNameFor(v_name_3461_);
v___x_3464_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_3462_, v___x_3423_);
v___x_3465_ = l_Lean_mkConst(v___x_3463_, v___x_3464_);
v___x_3466_ = l_Lean_mkAppN(v___x_3465_, v_xs_3412_);
v___x_3467_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_head_3459_, v___x_3466_, v___y_3415_);
lean_dec_ref(v___x_3467_);
v___x_3468_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__1(v_head_3460_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3470_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_a_3469_);
lean_dec_ref(v___x_3468_);
v___x_3470_ = l_Lean_MVarId_refl(v_a_3469_, v___x_3425_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_dec(v_name_3461_);
v___y_3428_ = v___x_3470_;
goto v___jp_3427_;
}
else
{
lean_object* v_a_3471_; uint8_t v___y_3473_; uint8_t v___x_3476_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
v___x_3476_ = l_Lean_Exception_isInterrupt(v_a_3471_);
if (v___x_3476_ == 0)
{
uint8_t v___x_3477_; 
v___x_3477_ = l_Lean_Exception_isRuntime(v_a_3471_);
v___y_3473_ = v___x_3477_;
goto v___jp_3472_;
}
else
{
lean_dec(v_a_3471_);
v___y_3473_ = v___x_3476_;
goto v___jp_3472_;
}
v___jp_3472_:
{
if (v___y_3473_ == 0)
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_dec_ref(v___x_3470_);
v___x_3474_ = l___private_Lean_Meta_Injective_0__Lean_Meta_injTheoremFailureHeader(v_name_3461_);
v___x_3475_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3474_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
v___y_3428_ = v___x_3475_;
goto v___jp_3427_;
}
else
{
lean_dec(v_name_3461_);
v___y_3428_ = v___x_3470_;
goto v___jp_3427_;
}
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec(v_name_3461_);
lean_dec(v_a_3421_);
v_a_3478_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3468_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3468_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
else
{
lean_dec_ref(v_tail_3456_);
lean_dec_ref(v_a_3442_);
lean_dec(v_a_3421_);
v___y_3444_ = v___y_3414_;
v___y_3445_ = v___y_3415_;
v___y_3446_ = v___y_3416_;
v___y_3447_ = v___y_3417_;
goto v___jp_3443_;
}
}
else
{
lean_dec_ref(v_a_3442_);
lean_dec(v_tail_3456_);
lean_dec(v_a_3421_);
v___y_3444_ = v___y_3414_;
v___y_3445_ = v___y_3415_;
v___y_3446_ = v___y_3416_;
v___y_3447_ = v___y_3417_;
goto v___jp_3443_;
}
}
else
{
lean_dec(v_a_3442_);
lean_dec(v_a_3421_);
v___y_3444_ = v___y_3414_;
v___y_3445_ = v___y_3415_;
v___y_3446_ = v___y_3416_;
v___y_3447_ = v___y_3417_;
goto v___jp_3443_;
}
v___jp_3443_:
{
lean_object* v_toConstantVal_3448_; lean_object* v_name_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v_toConstantVal_3448_ = lean_ctor_get(v_ctorVal_3411_, 0);
lean_inc_ref(v_toConstantVal_3448_);
lean_dec_ref(v_ctorVal_3411_);
v_name_3449_ = lean_ctor_get(v_toConstantVal_3448_, 0);
lean_inc(v_name_3449_);
lean_dec_ref(v_toConstantVal_3448_);
v___x_3450_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__6);
v___x_3451_ = l_Lean_MessageData_ofName(v_name_3449_);
v___x_3452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3450_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_3454_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
return v___x_3455_;
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec(v_a_3421_);
lean_dec_ref(v_ctorVal_3411_);
v_a_3486_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3441_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3441_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
v___jp_3427_:
{
if (lean_obj_tag(v___y_3428_) == 0)
{
uint8_t v___x_3429_; lean_object* v___x_3430_; 
lean_dec_ref(v___y_3428_);
v___x_3429_ = 1;
v___x_3430_ = l_Lean_Meta_mkLambdaFVars(v_xs_3412_, v_a_3421_, v___x_3426_, v___x_3425_, v___x_3426_, v___x_3425_, v___x_3429_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v___x_3430_;
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_dec(v_a_3421_);
v_a_3431_ = lean_ctor_get(v___y_3428_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___y_3428_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___y_3428_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___y_3428_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctorVal_3411_);
return v___x_3420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed(lean_object* v_ctorVal_3494_, lean_object* v_xs_3495_, lean_object* v_type_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0(v_ctorVal_3494_, v_xs_3495_, v_type_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec_ref(v_xs_3495_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(lean_object* v_ctorVal_3503_, lean_object* v_targetType_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v___f_3510_; uint8_t v___x_3511_; lean_object* v___x_3512_; 
v___f_3510_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3510_, 0, v_ctorVal_3503_);
v___x_3511_ = 0;
v___x_3512_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_targetType_3504_, v___f_3510_, v___x_3511_, v___x_3511_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___boxed(lean_object* v_ctorVal_3513_, lean_object* v_targetType_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3513_, v_targetType_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(lean_object* v_mvarId_3521_, lean_object* v_val_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___redArg(v_mvarId_3521_, v_val_3522_, v___y_3524_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0___boxed(lean_object* v_mvarId_3529_, lean_object* v_val_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0(v_mvarId_3529_, v_val_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0(lean_object* v_00_u03b2_3537_, lean_object* v_x_3538_, lean_object* v_x_3539_, lean_object* v_x_3540_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0___redArg(v_x_3538_, v_x_3539_, v_x_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3542_, lean_object* v_x_3543_, size_t v_x_3544_, size_t v_x_3545_, lean_object* v_x_3546_, lean_object* v_x_3547_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___redArg(v_x_3543_, v_x_3544_, v_x_3545_, v_x_3546_, v_x_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3549_, lean_object* v_x_3550_, lean_object* v_x_3551_, lean_object* v_x_3552_, lean_object* v_x_3553_, lean_object* v_x_3554_){
_start:
{
size_t v_x_5544__boxed_3555_; size_t v_x_5545__boxed_3556_; lean_object* v_res_3557_; 
v_x_5544__boxed_3555_ = lean_unbox_usize(v_x_3551_);
lean_dec(v_x_3551_);
v_x_5545__boxed_3556_ = lean_unbox_usize(v_x_3552_);
lean_dec(v_x_3552_);
v_res_3557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1(v_00_u03b2_3549_, v_x_3550_, v_x_5544__boxed_3555_, v_x_5545__boxed_3556_, v_x_3553_, v_x_3554_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3558_, lean_object* v_n_3559_, lean_object* v_k_3560_, lean_object* v_v_3561_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3___redArg(v_n_3559_, v_k_3560_, v_v_3561_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3563_, size_t v_depth_3564_, lean_object* v_keys_3565_, lean_object* v_vals_3566_, lean_object* v_heq_3567_, lean_object* v_i_3568_, lean_object* v_entries_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_3564_, v_keys_3565_, v_vals_3566_, v_i_3568_, v_entries_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_3571_, lean_object* v_depth_3572_, lean_object* v_keys_3573_, lean_object* v_vals_3574_, lean_object* v_heq_3575_, lean_object* v_i_3576_, lean_object* v_entries_3577_){
_start:
{
size_t v_depth_boxed_3578_; lean_object* v_res_3579_; 
v_depth_boxed_3578_ = lean_unbox_usize(v_depth_3572_);
lean_dec(v_depth_3572_);
v_res_3579_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_3571_, v_depth_boxed_3578_, v_keys_3573_, v_vals_3574_, v_heq_3575_, v_i_3576_, v_entries_3577_);
lean_dec_ref(v_vals_3574_);
lean_dec_ref(v_keys_3573_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3580_, lean_object* v_x_3581_, lean_object* v_x_3582_, lean_object* v_x_3583_, lean_object* v_x_3584_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_x_3581_, v_x_3582_, v_x_3583_, v_x_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(lean_object* v_ctorVal_3586_, lean_object* v_val_3587_, lean_object* v_name_3588_, lean_object* v_levelParams_3589_, uint8_t v___x_3590_, uint8_t v_hasTrace_3591_, lean_object* v_____r_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v___x_3598_; 
lean_inc_ref(v_val_3587_);
v___x_3598_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3586_, v_val_3587_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v_a_3601_; lean_object* v___x_3602_; lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3619_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref(v___x_3598_);
v___x_3600_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3587_, v___y_3594_);
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref(v___x_3600_);
v___x_3602_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3599_, v___y_3594_);
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3605_ = v___x_3602_;
v_isShared_3606_ = v_isSharedCheck_3619_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3602_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3619_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
lean_inc(v_name_3588_);
v___x_3607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3607_, 0, v_name_3588_);
lean_ctor_set(v___x_3607_, 1, v_levelParams_3589_);
lean_ctor_set(v___x_3607_, 2, v_a_3601_);
v___x_3608_ = lean_box(0);
lean_inc(v_name_3588_);
v___x_3609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3609_, 0, v_name_3588_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3607_);
lean_ctor_set(v___x_3610_, 1, v_a_3603_);
lean_ctor_set(v___x_3610_, 2, v___x_3609_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set_tag(v___x_3605_, 2);
lean_ctor_set(v___x_3605_, 0, v___x_3610_);
v___x_3612_ = v___x_3605_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_addDecl(v___x_3612_, v___x_3590_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v___x_3614_; uint8_t v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
lean_dec_ref(v___x_3613_);
v___x_3614_ = l_Lean_Meta_simpExtension;
v___x_3615_ = 0;
v___x_3616_ = lean_unsigned_to_nat(1000u);
v___x_3617_ = l_Lean_Meta_addSimpTheorem(v___x_3614_, v_name_3588_, v_hasTrace_3591_, v___x_3590_, v___x_3615_, v___x_3616_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
return v___x_3617_;
}
else
{
lean_dec(v_name_3588_);
return v___x_3613_;
}
}
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_dec(v_levelParams_3589_);
lean_dec(v_name_3588_);
lean_dec_ref(v_val_3587_);
v_a_3620_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3598_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3598_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1___boxed(lean_object* v_ctorVal_3628_, lean_object* v_val_3629_, lean_object* v_name_3630_, lean_object* v_levelParams_3631_, lean_object* v___x_3632_, lean_object* v_hasTrace_3633_, lean_object* v_____r_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
uint8_t v___x_6738__boxed_3640_; uint8_t v_hasTrace_boxed_3641_; lean_object* v_res_3642_; 
v___x_6738__boxed_3640_ = lean_unbox(v___x_3632_);
v_hasTrace_boxed_3641_ = lean_unbox(v_hasTrace_3633_);
v_res_3642_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3628_, v_val_3629_, v_name_3630_, v_levelParams_3631_, v___x_6738__boxed_3640_, v_hasTrace_boxed_3641_, v_____r_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(lean_object* v_ctorVal_3643_, lean_object* v_val_3644_, lean_object* v_name_3645_, lean_object* v_levelParams_3646_, uint8_t v___x_3647_, lean_object* v_____r_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; 
lean_inc_ref(v_val_3644_);
v___x_3654_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3643_, v_val_3644_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3656_; lean_object* v_a_3657_; lean_object* v___x_3658_; lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3676_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3655_);
lean_dec_ref(v___x_3654_);
v___x_3656_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3644_, v___y_3650_);
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref(v___x_3656_);
v___x_3658_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3655_, v___y_3650_);
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3661_ = v___x_3658_;
v_isShared_3662_ = v_isSharedCheck_3676_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3658_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3676_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3668_; 
lean_inc(v_name_3645_);
v___x_3663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3663_, 0, v_name_3645_);
lean_ctor_set(v___x_3663_, 1, v_levelParams_3646_);
lean_ctor_set(v___x_3663_, 2, v_a_3657_);
v___x_3664_ = lean_box(0);
lean_inc(v_name_3645_);
v___x_3665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3665_, 0, v_name_3645_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v___x_3666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3663_);
lean_ctor_set(v___x_3666_, 1, v_a_3659_);
lean_ctor_set(v___x_3666_, 2, v___x_3665_);
if (v_isShared_3662_ == 0)
{
lean_ctor_set_tag(v___x_3661_, 2);
lean_ctor_set(v___x_3661_, 0, v___x_3666_);
v___x_3668_ = v___x_3661_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
uint8_t v___x_3669_; lean_object* v___x_3670_; 
v___x_3669_ = 0;
v___x_3670_ = l_Lean_addDecl(v___x_3668_, v___x_3669_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v___x_3671_; uint8_t v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
lean_dec_ref(v___x_3670_);
v___x_3671_ = l_Lean_Meta_simpExtension;
v___x_3672_ = 0;
v___x_3673_ = lean_unsigned_to_nat(1000u);
v___x_3674_ = l_Lean_Meta_addSimpTheorem(v___x_3671_, v_name_3645_, v___x_3647_, v___x_3669_, v___x_3672_, v___x_3673_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
return v___x_3674_;
}
else
{
lean_dec(v_name_3645_);
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec(v_levelParams_3646_);
lean_dec(v_name_3645_);
lean_dec_ref(v_val_3644_);
v_a_3677_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3654_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3654_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0___boxed(lean_object* v_ctorVal_3685_, lean_object* v_val_3686_, lean_object* v_name_3687_, lean_object* v_levelParams_3688_, lean_object* v___x_3689_, lean_object* v_____r_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
uint8_t v___x_6826__boxed_3696_; lean_object* v_res_3697_; 
v___x_6826__boxed_3696_ = lean_unbox(v___x_3689_);
v_res_3697_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3685_, v_val_3686_, v_name_3687_, v_levelParams_3688_, v___x_6826__boxed_3696_, v_____r_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(lean_object* v_ctorVal_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v_toConstantVal_3704_; lean_object* v_options_3705_; lean_object* v_name_3706_; lean_object* v_levelParams_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3954_; 
v_toConstantVal_3704_ = lean_ctor_get(v_ctorVal_3698_, 0);
lean_inc_ref(v_toConstantVal_3704_);
v_options_3705_ = lean_ctor_get(v_a_3701_, 2);
v_name_3706_ = lean_ctor_get(v_toConstantVal_3704_, 0);
v_levelParams_3707_ = lean_ctor_get(v_toConstantVal_3704_, 1);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_toConstantVal_3704_);
if (v_isSharedCheck_3954_ == 0)
{
lean_object* v_unused_3955_; 
v_unused_3955_ = lean_ctor_get(v_toConstantVal_3704_, 2);
lean_dec(v_unused_3955_);
v___x_3709_ = v_toConstantVal_3704_;
v_isShared_3710_ = v_isSharedCheck_3954_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_levelParams_3707_);
lean_inc(v_name_3706_);
lean_dec(v_toConstantVal_3704_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3954_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
uint8_t v_hasTrace_3711_; lean_object* v_name_3712_; lean_object* v_cls_3713_; 
v_hasTrace_3711_ = lean_ctor_get_uint8(v_options_3705_, sizeof(void*)*1);
v_name_3712_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_3706_);
v_cls_3713_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
if (v_hasTrace_3711_ == 0)
{
lean_object* v___x_3714_; 
lean_inc_ref(v_ctorVal_3698_);
v___x_3714_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3769_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3717_ = v___x_3714_;
v_isShared_3718_ = v_isSharedCheck_3769_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3714_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3769_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
if (lean_obj_tag(v_a_3715_) == 1)
{
lean_object* v_val_3719_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___x_3758_; lean_object* v_a_3759_; uint8_t v___x_3760_; 
lean_del_object(v___x_3717_);
v_val_3719_ = lean_ctor_get(v_a_3715_, 0);
lean_inc(v_val_3719_);
lean_dec_ref(v_a_3715_);
v___x_3758_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_3713_, v_a_3701_);
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref(v___x_3758_);
v___x_3760_ = lean_unbox(v_a_3759_);
lean_dec(v_a_3759_);
if (v___x_3760_ == 0)
{
v___y_3721_ = v_a_3699_;
v___y_3722_ = v_a_3700_;
v___y_3723_ = v_a_3701_;
v___y_3724_ = v_a_3702_;
goto v___jp_3720_;
}
else
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3761_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_3719_);
v___x_3762_ = l_Lean_MessageData_ofExpr(v_val_3719_);
v___x_3763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3761_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v___x_3764_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_3713_, v___x_3763_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_dec_ref(v___x_3764_);
v___y_3721_ = v_a_3699_;
v___y_3722_ = v_a_3700_;
v___y_3723_ = v_a_3701_;
v___y_3724_ = v_a_3702_;
goto v___jp_3720_;
}
else
{
lean_dec(v_val_3719_);
lean_dec(v_name_3712_);
lean_del_object(v___x_3709_);
lean_dec(v_levelParams_3707_);
lean_dec_ref(v_ctorVal_3698_);
return v___x_3764_;
}
}
v___jp_3720_:
{
lean_object* v___x_3725_; 
lean_inc(v_val_3719_);
v___x_3725_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3698_, v_val_3719_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; lean_object* v___x_3727_; lean_object* v_a_3728_; lean_object* v___x_3729_; lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3749_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref(v___x_3725_);
v___x_3727_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3719_, v___y_3722_);
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref(v___x_3727_);
v___x_3729_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3726_, v___y_3722_);
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3732_ = v___x_3729_;
v_isShared_3733_ = v_isSharedCheck_3749_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3729_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3749_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
lean_inc(v_name_3712_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 2, v_a_3728_);
lean_ctor_set(v___x_3709_, 0, v_name_3712_);
v___x_3735_ = v___x_3709_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_name_3712_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_levelParams_3707_);
lean_ctor_set(v_reuseFailAlloc_3748_, 2, v_a_3728_);
v___x_3735_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3740_; 
v___x_3736_ = lean_box(0);
lean_inc(v_name_3712_);
v___x_3737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3737_, 0, v_name_3712_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3735_);
lean_ctor_set(v___x_3738_, 1, v_a_3730_);
lean_ctor_set(v___x_3738_, 2, v___x_3737_);
if (v_isShared_3733_ == 0)
{
lean_ctor_set_tag(v___x_3732_, 2);
lean_ctor_set(v___x_3732_, 0, v___x_3738_);
v___x_3740_ = v___x_3732_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_Lean_addDecl(v___x_3740_, v_hasTrace_3711_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v___x_3742_; uint8_t v___x_3743_; uint8_t v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_dec_ref(v___x_3741_);
v___x_3742_ = l_Lean_Meta_simpExtension;
v___x_3743_ = 1;
v___x_3744_ = 0;
v___x_3745_ = lean_unsigned_to_nat(1000u);
v___x_3746_ = l_Lean_Meta_addSimpTheorem(v___x_3742_, v_name_3712_, v___x_3743_, v_hasTrace_3711_, v___x_3744_, v___x_3745_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
return v___x_3746_;
}
else
{
lean_dec(v_name_3712_);
return v___x_3741_;
}
}
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec(v_val_3719_);
lean_dec(v_name_3712_);
lean_del_object(v___x_3709_);
lean_dec(v_levelParams_3707_);
v_a_3750_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3725_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3725_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
else
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
lean_dec(v_a_3715_);
lean_dec(v_name_3712_);
lean_del_object(v___x_3709_);
lean_dec(v_levelParams_3707_);
lean_dec_ref(v_ctorVal_3698_);
v___x_3765_ = lean_box(0);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_3765_);
v___x_3767_ = v___x_3717_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3765_);
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
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec(v_name_3712_);
lean_del_object(v___x_3709_);
lean_dec(v_levelParams_3707_);
lean_dec_ref(v_ctorVal_3698_);
v_a_3770_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3714_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3714_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
else
{
lean_object* v___x_3778_; lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3953_; 
v___x_3778_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_3713_, v_a_3701_);
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3781_ = v___x_3778_;
v_isShared_3782_ = v_isSharedCheck_3953_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3778_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3953_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___f_3783_; lean_object* v___x_3784_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v_a_3788_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v_a_3801_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v_a_3808_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v_a_3819_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v_a_3835_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v_a_3840_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; uint8_t v___x_3887_; 
lean_inc(v_name_3712_);
v___f_3783_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3783_, 0, v_name_3712_);
v___x_3784_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__1));
v___x_3887_ = lean_unbox(v_a_3779_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3888_ = l_Lean_trace_profiler;
v___x_3889_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3705_, v___x_3888_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; 
lean_dec_ref(v___f_3783_);
lean_del_object(v___x_3781_);
lean_dec(v_a_3779_);
lean_inc_ref(v_ctorVal_3698_);
v___x_3890_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3944_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3893_ = v___x_3890_;
v_isShared_3894_ = v_isSharedCheck_3944_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3890_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3944_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
if (lean_obj_tag(v_a_3891_) == 1)
{
lean_object* v_val_3895_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___x_3933_; lean_object* v_a_3934_; uint8_t v___x_3935_; 
lean_del_object(v___x_3893_);
v_val_3895_ = lean_ctor_get(v_a_3891_, 0);
lean_inc(v_val_3895_);
lean_dec_ref(v_a_3891_);
v___x_3933_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_3713_, v_a_3701_);
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref(v___x_3933_);
v___x_3935_ = lean_unbox(v_a_3934_);
lean_dec(v_a_3934_);
if (v___x_3935_ == 0)
{
v___y_3897_ = v_a_3699_;
v___y_3898_ = v_a_3700_;
v___y_3899_ = v_a_3701_;
v___y_3900_ = v_a_3702_;
goto v___jp_3896_;
}
else
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3936_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_3895_);
v___x_3937_ = l_Lean_MessageData_ofExpr(v_val_3895_);
v___x_3938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3936_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
v___x_3939_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_3713_, v___x_3938_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_dec_ref(v___x_3939_);
v___y_3897_ = v_a_3699_;
v___y_3898_ = v_a_3700_;
v___y_3899_ = v_a_3701_;
v___y_3900_ = v_a_3702_;
goto v___jp_3896_;
}
else
{
lean_dec(v_val_3895_);
lean_dec(v_name_3712_);
lean_del_object(v___x_3709_);
lean_dec(v_levelParams_3707_);
lean_dec_ref(v_ctorVal_3698_);
return v___x_3939_;
}
}
v___jp_3896_:
{
lean_object* v___x_3901_; 
lean_inc(v_val_3895_);
v___x_3901_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue(v_ctorVal_3698_, v_val_3895_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3903_; lean_object* v_a_3904_; lean_object* v___x_3905_; lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3924_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3902_);
lean_dec_ref(v___x_3901_);
v___x_3903_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_val_3895_, v___y_3898_);
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref(v___x_3903_);
v___x_3905_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v_a_3902_, v___y_3898_);
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3908_ = v___x_3905_;
v_isShared_3909_ = v_isSharedCheck_3924_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3905_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3924_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
lean_inc(v_name_3712_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 2, v_a_3904_);
lean_ctor_set(v___x_3709_, 0, v_name_3712_);
v___x_3911_ = v___x_3709_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_name_3712_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v_levelParams_3707_);
lean_ctor_set(v_reuseFailAlloc_3923_, 2, v_a_3904_);
v___x_3911_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3916_; 
v___x_3912_ = lean_box(0);
lean_inc(v_name_3712_);
v___x_3913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3913_, 0, v_name_3712_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3911_);
lean_ctor_set(v___x_3914_, 1, v_a_3906_);
lean_ctor_set(v___x_3914_, 2, v___x_3913_);
if (v_isShared_3909_ == 0)
{
lean_ctor_set_tag(v___x_3908_, 2);
lean_ctor_set(v___x_3908_, 0, v___x_3914_);
v___x_3916_ = v___x_3908_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Lean_addDecl(v___x_3916_, v___x_3889_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v___x_3918_; uint8_t v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
lean_dec_ref(v___x_3917_);
v___x_3918_ = l_Lean_Meta_simpExtension;
v___x_3919_ = 0;
v___x_3920_ = lean_unsigned_to_nat(1000u);
v___x_3921_ = l_Lean_Meta_addSimpTheorem(v___x_3918_, v_name_3712_, v_hasTrace_3711_, v___x_3889_, v___x_3919_, v___x_3920_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
return v___x_3921_;
}
else
{
lean_dec(v_name_3712_);
return v___x_3917_;
}
}
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec(v_val_3895_);
lean_dec(v_name_3712_);
lean_del_object(v___x_3709_);
lean_dec(v_levelParams_3707_);
v_a_3925_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3901_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3901_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
else
{
lean_object* v___x_3940_; lean_object* v___x_3942_; 
lean_dec(v_a_3891_);
lean_dec(v_name_3712_);
lean_del_object(v___x_3709_);
lean_dec(v_levelParams_3707_);
lean_dec_ref(v_ctorVal_3698_);
v___x_3940_ = lean_box(0);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3940_);
v___x_3942_ = v___x_3893_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
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
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec(v_name_3712_);
lean_del_object(v___x_3709_);
lean_dec(v_levelParams_3707_);
lean_dec_ref(v_ctorVal_3698_);
v_a_3945_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3890_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3890_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
else
{
lean_del_object(v___x_3709_);
goto v___jp_3848_;
}
}
else
{
lean_del_object(v___x_3709_);
goto v___jp_3848_;
}
v___jp_3785_:
{
lean_object* v___x_3789_; double v___x_3790_; double v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; uint8_t v___x_3796_; lean_object* v___x_3797_; 
v___x_3789_ = lean_io_get_num_heartbeats();
v___x_3790_ = lean_float_of_nat(v___y_3787_);
v___x_3791_ = lean_float_of_nat(v___x_3789_);
v___x_3792_ = lean_box_float(v___x_3790_);
v___x_3793_ = lean_box_float(v___x_3791_);
v___x_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3792_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
v___x_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3795_, 0, v_a_3788_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_unbox(v_a_3779_);
lean_dec(v_a_3779_);
v___x_3797_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3713_, v_hasTrace_3711_, v___x_3784_, v_options_3705_, v___x_3796_, v___y_3786_, v___f_3783_, v___x_3795_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
return v___x_3797_;
}
v___jp_3798_:
{
lean_object* v___x_3803_; 
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v_a_3801_);
v___x_3803_ = v___x_3781_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3801_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
v___y_3786_ = v___y_3799_;
v___y_3787_ = v___y_3800_;
v_a_3788_ = v___x_3803_;
goto v___jp_3785_;
}
}
v___jp_3805_:
{
lean_object* v___x_3809_; 
v___x_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3809_, 0, v_a_3808_);
v___y_3786_ = v___y_3806_;
v___y_3787_ = v___y_3807_;
v_a_3788_ = v___x_3809_;
goto v___jp_3785_;
}
v___jp_3810_:
{
if (lean_obj_tag(v___y_3813_) == 0)
{
lean_object* v_a_3814_; 
lean_del_object(v___x_3781_);
v_a_3814_ = lean_ctor_get(v___y_3813_, 0);
lean_inc(v_a_3814_);
lean_dec_ref(v___y_3813_);
v___y_3806_ = v___y_3811_;
v___y_3807_ = v___y_3812_;
v_a_3808_ = v_a_3814_;
goto v___jp_3805_;
}
else
{
lean_object* v_a_3815_; 
v_a_3815_ = lean_ctor_get(v___y_3813_, 0);
lean_inc(v_a_3815_);
lean_dec_ref(v___y_3813_);
v___y_3799_ = v___y_3811_;
v___y_3800_ = v___y_3812_;
v_a_3801_ = v_a_3815_;
goto v___jp_3798_;
}
}
v___jp_3816_:
{
lean_object* v___x_3820_; double v___x_3821_; double v___x_3822_; double v___x_3823_; double v___x_3824_; double v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; lean_object* v___x_3831_; 
v___x_3820_ = lean_io_mono_nanos_now();
v___x_3821_ = lean_float_of_nat(v___y_3818_);
v___x_3822_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_3823_ = lean_float_div(v___x_3821_, v___x_3822_);
v___x_3824_ = lean_float_of_nat(v___x_3820_);
v___x_3825_ = lean_float_div(v___x_3824_, v___x_3822_);
v___x_3826_ = lean_box_float(v___x_3823_);
v___x_3827_ = lean_box_float(v___x_3825_);
v___x_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3826_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
v___x_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3829_, 0, v_a_3819_);
lean_ctor_set(v___x_3829_, 1, v___x_3828_);
v___x_3830_ = lean_unbox(v_a_3779_);
lean_dec(v_a_3779_);
v___x_3831_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v_cls_3713_, v_hasTrace_3711_, v___x_3784_, v_options_3705_, v___x_3830_, v___y_3817_, v___f_3783_, v___x_3829_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
return v___x_3831_;
}
v___jp_3832_:
{
lean_object* v___x_3836_; 
v___x_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3836_, 0, v_a_3835_);
v___y_3817_ = v___y_3833_;
v___y_3818_ = v___y_3834_;
v_a_3819_ = v___x_3836_;
goto v___jp_3816_;
}
v___jp_3837_:
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3841_, 0, v_a_3840_);
v___y_3817_ = v___y_3838_;
v___y_3818_ = v___y_3839_;
v_a_3819_ = v___x_3841_;
goto v___jp_3816_;
}
v___jp_3842_:
{
if (lean_obj_tag(v___y_3845_) == 0)
{
lean_object* v_a_3846_; 
v_a_3846_ = lean_ctor_get(v___y_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref(v___y_3845_);
v___y_3833_ = v___y_3843_;
v___y_3834_ = v___y_3844_;
v_a_3835_ = v_a_3846_;
goto v___jp_3832_;
}
else
{
lean_object* v_a_3847_; 
v_a_3847_ = lean_ctor_get(v___y_3845_, 0);
lean_inc(v_a_3847_);
lean_dec_ref(v___y_3845_);
v___y_3838_ = v___y_3843_;
v___y_3839_ = v___y_3844_;
v_a_3840_ = v_a_3847_;
goto v___jp_3837_;
}
}
v___jp_3848_:
{
lean_object* v___x_3849_; lean_object* v_a_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; 
v___x_3849_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_3702_);
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref(v___x_3849_);
v___x_3851_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3852_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_3705_, v___x_3851_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
lean_del_object(v___x_3781_);
v___x_3853_ = lean_io_mono_nanos_now();
lean_inc_ref(v_ctorVal_3698_);
v___x_3854_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref(v___x_3854_);
if (lean_obj_tag(v_a_3855_) == 1)
{
lean_object* v_val_3856_; lean_object* v___x_3857_; lean_object* v_a_3858_; uint8_t v___x_3859_; 
v_val_3856_ = lean_ctor_get(v_a_3855_, 0);
lean_inc(v_val_3856_);
lean_dec_ref(v_a_3855_);
v___x_3857_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_3713_, v_a_3701_);
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref(v___x_3857_);
v___x_3859_ = lean_unbox(v_a_3858_);
lean_dec(v_a_3858_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = lean_box(0);
v___x_3861_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3698_, v_val_3856_, v_name_3712_, v_levelParams_3707_, v___x_3852_, v_hasTrace_3711_, v___x_3860_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
v___y_3843_ = v_a_3850_;
v___y_3844_ = v___x_3853_;
v___y_3845_ = v___x_3861_;
goto v___jp_3842_;
}
else
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3862_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_3856_);
v___x_3863_ = l_Lean_MessageData_ofExpr(v_val_3856_);
v___x_3864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3862_);
lean_ctor_set(v___x_3864_, 1, v___x_3863_);
v___x_3865_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_3713_, v___x_3864_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v___x_3867_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
lean_dec_ref(v___x_3865_);
v___x_3867_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__1(v_ctorVal_3698_, v_val_3856_, v_name_3712_, v_levelParams_3707_, v___x_3852_, v_hasTrace_3711_, v_a_3866_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
v___y_3843_ = v_a_3850_;
v___y_3844_ = v___x_3853_;
v___y_3845_ = v___x_3867_;
goto v___jp_3842_;
}
else
{
lean_dec(v_val_3856_);
lean_dec(v_name_3712_);
lean_dec(v_levelParams_3707_);
lean_dec_ref(v_ctorVal_3698_);
v___y_3843_ = v_a_3850_;
v___y_3844_ = v___x_3853_;
v___y_3845_ = v___x_3865_;
goto v___jp_3842_;
}
}
}
else
{
lean_object* v___x_3868_; 
lean_dec(v_a_3855_);
lean_dec(v_name_3712_);
lean_dec(v_levelParams_3707_);
lean_dec_ref(v_ctorVal_3698_);
v___x_3868_ = lean_box(0);
v___y_3833_ = v_a_3850_;
v___y_3834_ = v___x_3853_;
v_a_3835_ = v___x_3868_;
goto v___jp_3832_;
}
}
else
{
lean_object* v_a_3869_; 
lean_dec(v_name_3712_);
lean_dec(v_levelParams_3707_);
lean_dec_ref(v_ctorVal_3698_);
v_a_3869_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3869_);
lean_dec_ref(v___x_3854_);
v___y_3838_ = v_a_3850_;
v___y_3839_ = v___x_3853_;
v_a_3840_ = v_a_3869_;
goto v___jp_3837_;
}
}
else
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_ctorVal_3698_);
v___x_3871_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremType_x3f(v_ctorVal_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref(v___x_3871_);
if (lean_obj_tag(v_a_3872_) == 1)
{
lean_object* v_val_3873_; lean_object* v___x_3874_; lean_object* v_a_3875_; uint8_t v___x_3876_; 
v_val_3873_ = lean_ctor_get(v_a_3872_, 0);
lean_inc(v_val_3873_);
lean_dec_ref(v_a_3872_);
v___x_3874_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v_cls_3713_, v_a_3701_);
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref(v___x_3874_);
v___x_3876_ = lean_unbox(v_a_3875_);
lean_dec(v_a_3875_);
if (v___x_3876_ == 0)
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = lean_box(0);
v___x_3878_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3698_, v_val_3873_, v_name_3712_, v_levelParams_3707_, v___x_3852_, v___x_3877_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
v___y_3811_ = v_a_3850_;
v___y_3812_ = v___x_3870_;
v___y_3813_ = v___x_3878_;
goto v___jp_3810_;
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3879_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__1);
lean_inc(v_val_3873_);
v___x_3880_ = l_Lean_MessageData_ofExpr(v_val_3873_);
v___x_3881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3879_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___x_3882_ = l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2(v_cls_3713_, v___x_3881_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3884_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref(v___x_3882_);
v___x_3884_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___lam__0(v_ctorVal_3698_, v_val_3873_, v_name_3712_, v_levelParams_3707_, v___x_3852_, v_a_3883_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_);
v___y_3811_ = v_a_3850_;
v___y_3812_ = v___x_3870_;
v___y_3813_ = v___x_3884_;
goto v___jp_3810_;
}
else
{
lean_dec(v_val_3873_);
lean_dec(v_name_3712_);
lean_dec(v_levelParams_3707_);
lean_dec_ref(v_ctorVal_3698_);
v___y_3811_ = v_a_3850_;
v___y_3812_ = v___x_3870_;
v___y_3813_ = v___x_3882_;
goto v___jp_3810_;
}
}
}
else
{
lean_object* v___x_3885_; 
lean_dec(v_a_3872_);
lean_del_object(v___x_3781_);
lean_dec(v_name_3712_);
lean_dec(v_levelParams_3707_);
lean_dec_ref(v_ctorVal_3698_);
v___x_3885_ = lean_box(0);
v___y_3806_ = v_a_3850_;
v___y_3807_ = v___x_3870_;
v_a_3808_ = v___x_3885_;
goto v___jp_3805_;
}
}
else
{
lean_object* v_a_3886_; 
lean_dec(v_name_3712_);
lean_dec(v_levelParams_3707_);
lean_dec_ref(v_ctorVal_3698_);
v_a_3886_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3886_);
lean_dec_ref(v___x_3871_);
v___y_3799_ = v_a_3850_;
v___y_3800_ = v___x_3870_;
v_a_3801_ = v_a_3886_;
goto v___jp_3798_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem___boxed(lean_object* v_ctorVal_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v_res_3962_; 
v_res_3962_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_ctorVal_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_);
lean_dec(v_a_3960_);
lean_dec_ref(v_a_3959_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(lean_object* v_name_3963_, lean_object* v_decl_3964_, lean_object* v_ref_3965_){
_start:
{
lean_object* v_defValue_3967_; lean_object* v_descr_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3995_; 
v_defValue_3967_ = lean_ctor_get(v_decl_3964_, 0);
v_descr_3968_ = lean_ctor_get(v_decl_3964_, 1);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_decl_3964_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3970_ = v_decl_3964_;
v_isShared_3971_ = v_isSharedCheck_3995_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_descr_3968_);
lean_inc(v_defValue_3967_);
lean_dec(v_decl_3964_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3995_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3972_; uint8_t v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3972_ = lean_alloc_ctor(1, 0, 1);
v___x_3973_ = lean_unbox(v_defValue_3967_);
lean_ctor_set_uint8(v___x_3972_, 0, v___x_3973_);
lean_inc(v_name_3963_);
v___x_3974_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3974_, 0, v_name_3963_);
lean_ctor_set(v___x_3974_, 1, v_ref_3965_);
lean_ctor_set(v___x_3974_, 2, v___x_3972_);
lean_ctor_set(v___x_3974_, 3, v_descr_3968_);
lean_inc(v_name_3963_);
v___x_3975_ = lean_register_option(v_name_3963_, v___x_3974_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3985_; 
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3985_ == 0)
{
lean_object* v_unused_3986_; 
v_unused_3986_ = lean_ctor_get(v___x_3975_, 0);
lean_dec(v_unused_3986_);
v___x_3977_ = v___x_3975_;
v_isShared_3978_ = v_isSharedCheck_3985_;
goto v_resetjp_3976_;
}
else
{
lean_dec(v___x_3975_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3985_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 1, v_defValue_3967_);
lean_ctor_set(v___x_3970_, 0, v_name_3963_);
v___x_3980_ = v___x_3970_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_name_3963_);
lean_ctor_set(v_reuseFailAlloc_3984_, 1, v_defValue_3967_);
v___x_3980_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
lean_object* v___x_3982_; 
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v___x_3980_);
v___x_3982_ = v___x_3977_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3980_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_del_object(v___x_3970_);
lean_dec(v_defValue_3967_);
lean_dec(v_name_3963_);
v_a_3987_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3975_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3975_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_3996_, lean_object* v_decl_3997_, lean_object* v_ref_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v_name_3996_, v_decl_3997_, v_ref_3998_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4014_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4015_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4016_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_));
v___x_4017_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4__spec__0(v___x_4014_, v___x_4015_, v___x_4016_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4____boxed(lean_object* v_a_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4151801446____hygCtx___hyg_4_();
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(lean_object* v___y_4020_, uint8_t v_isExporting_4021_, lean_object* v___x_4022_, lean_object* v___y_4023_, lean_object* v___x_4024_, lean_object* v_a_x3f_4025_){
_start:
{
lean_object* v___x_4027_; lean_object* v_env_4028_; lean_object* v_nextMacroScope_4029_; lean_object* v_ngen_4030_; lean_object* v_auxDeclNGen_4031_; lean_object* v_traceState_4032_; lean_object* v_messages_4033_; lean_object* v_infoState_4034_; lean_object* v_snapshotTasks_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4060_; 
v___x_4027_ = lean_st_ref_take(v___y_4020_);
v_env_4028_ = lean_ctor_get(v___x_4027_, 0);
v_nextMacroScope_4029_ = lean_ctor_get(v___x_4027_, 1);
v_ngen_4030_ = lean_ctor_get(v___x_4027_, 2);
v_auxDeclNGen_4031_ = lean_ctor_get(v___x_4027_, 3);
v_traceState_4032_ = lean_ctor_get(v___x_4027_, 4);
v_messages_4033_ = lean_ctor_get(v___x_4027_, 6);
v_infoState_4034_ = lean_ctor_get(v___x_4027_, 7);
v_snapshotTasks_4035_ = lean_ctor_get(v___x_4027_, 8);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4060_ == 0)
{
lean_object* v_unused_4061_; 
v_unused_4061_ = lean_ctor_get(v___x_4027_, 5);
lean_dec(v_unused_4061_);
v___x_4037_ = v___x_4027_;
v_isShared_4038_ = v_isSharedCheck_4060_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_snapshotTasks_4035_);
lean_inc(v_infoState_4034_);
lean_inc(v_messages_4033_);
lean_inc(v_traceState_4032_);
lean_inc(v_auxDeclNGen_4031_);
lean_inc(v_ngen_4030_);
lean_inc(v_nextMacroScope_4029_);
lean_inc(v_env_4028_);
lean_dec(v___x_4027_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4060_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4039_; lean_object* v___x_4041_; 
v___x_4039_ = l_Lean_Environment_setExporting(v_env_4028_, v_isExporting_4021_);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 5, v___x_4022_);
lean_ctor_set(v___x_4037_, 0, v___x_4039_);
v___x_4041_ = v___x_4037_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v_nextMacroScope_4029_);
lean_ctor_set(v_reuseFailAlloc_4059_, 2, v_ngen_4030_);
lean_ctor_set(v_reuseFailAlloc_4059_, 3, v_auxDeclNGen_4031_);
lean_ctor_set(v_reuseFailAlloc_4059_, 4, v_traceState_4032_);
lean_ctor_set(v_reuseFailAlloc_4059_, 5, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4059_, 6, v_messages_4033_);
lean_ctor_set(v_reuseFailAlloc_4059_, 7, v_infoState_4034_);
lean_ctor_set(v_reuseFailAlloc_4059_, 8, v_snapshotTasks_4035_);
v___x_4041_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v_mctx_4044_; lean_object* v_zetaDeltaFVarIds_4045_; lean_object* v_postponed_4046_; lean_object* v_diag_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4057_; 
v___x_4042_ = lean_st_ref_set(v___y_4020_, v___x_4041_);
v___x_4043_ = lean_st_ref_take(v___y_4023_);
v_mctx_4044_ = lean_ctor_get(v___x_4043_, 0);
v_zetaDeltaFVarIds_4045_ = lean_ctor_get(v___x_4043_, 2);
v_postponed_4046_ = lean_ctor_get(v___x_4043_, 3);
v_diag_4047_ = lean_ctor_get(v___x_4043_, 4);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4057_ == 0)
{
lean_object* v_unused_4058_; 
v_unused_4058_ = lean_ctor_get(v___x_4043_, 1);
lean_dec(v_unused_4058_);
v___x_4049_ = v___x_4043_;
v_isShared_4050_ = v_isSharedCheck_4057_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_diag_4047_);
lean_inc(v_postponed_4046_);
lean_inc(v_zetaDeltaFVarIds_4045_);
lean_inc(v_mctx_4044_);
lean_dec(v___x_4043_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4057_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 1, v___x_4024_);
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_mctx_4044_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v___x_4024_);
lean_ctor_set(v_reuseFailAlloc_4056_, 2, v_zetaDeltaFVarIds_4045_);
lean_ctor_set(v_reuseFailAlloc_4056_, 3, v_postponed_4046_);
lean_ctor_set(v_reuseFailAlloc_4056_, 4, v_diag_4047_);
v___x_4052_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4053_ = lean_st_ref_set(v___y_4023_, v___x_4052_);
v___x_4054_ = lean_box(0);
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
return v___x_4055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0___boxed(lean_object* v___y_4062_, lean_object* v_isExporting_4063_, lean_object* v___x_4064_, lean_object* v___y_4065_, lean_object* v___x_4066_, lean_object* v_a_x3f_4067_, lean_object* v___y_4068_){
_start:
{
uint8_t v_isExporting_boxed_4069_; lean_object* v_res_4070_; 
v_isExporting_boxed_4069_ = lean_unbox(v_isExporting_4063_);
v_res_4070_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4062_, v_isExporting_boxed_4069_, v___x_4064_, v___y_4065_, v___x_4066_, v_a_x3f_4067_);
lean_dec(v_a_x3f_4067_);
lean_dec(v___y_4065_);
lean_dec(v___y_4062_);
return v_res_4070_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4071_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__0);
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
return v___x_4073_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4074_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
lean_ctor_set(v___x_4075_, 1, v___x_4074_);
return v___x_4075_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__1);
v___x_4077_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
lean_ctor_set(v___x_4077_, 2, v___x_4076_);
lean_ctor_set(v___x_4077_, 3, v___x_4076_);
lean_ctor_set(v___x_4077_, 4, v___x_4076_);
lean_ctor_set(v___x_4077_, 5, v___x_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(lean_object* v_x_4078_, uint8_t v_isExporting_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v___x_4085_; lean_object* v_env_4086_; uint8_t v_isExporting_4087_; lean_object* v___x_4088_; lean_object* v_env_4089_; lean_object* v_nextMacroScope_4090_; lean_object* v_ngen_4091_; lean_object* v_auxDeclNGen_4092_; lean_object* v_traceState_4093_; lean_object* v_messages_4094_; lean_object* v_infoState_4095_; lean_object* v_snapshotTasks_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4150_; 
v___x_4085_ = lean_st_ref_get(v___y_4083_);
v_env_4086_ = lean_ctor_get(v___x_4085_, 0);
lean_inc_ref(v_env_4086_);
lean_dec(v___x_4085_);
v_isExporting_4087_ = lean_ctor_get_uint8(v_env_4086_, sizeof(void*)*8);
lean_dec_ref(v_env_4086_);
v___x_4088_ = lean_st_ref_take(v___y_4083_);
v_env_4089_ = lean_ctor_get(v___x_4088_, 0);
v_nextMacroScope_4090_ = lean_ctor_get(v___x_4088_, 1);
v_ngen_4091_ = lean_ctor_get(v___x_4088_, 2);
v_auxDeclNGen_4092_ = lean_ctor_get(v___x_4088_, 3);
v_traceState_4093_ = lean_ctor_get(v___x_4088_, 4);
v_messages_4094_ = lean_ctor_get(v___x_4088_, 6);
v_infoState_4095_ = lean_ctor_get(v___x_4088_, 7);
v_snapshotTasks_4096_ = lean_ctor_get(v___x_4088_, 8);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4150_ == 0)
{
lean_object* v_unused_4151_; 
v_unused_4151_ = lean_ctor_get(v___x_4088_, 5);
lean_dec(v_unused_4151_);
v___x_4098_ = v___x_4088_;
v_isShared_4099_ = v_isSharedCheck_4150_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_snapshotTasks_4096_);
lean_inc(v_infoState_4095_);
lean_inc(v_messages_4094_);
lean_inc(v_traceState_4093_);
lean_inc(v_auxDeclNGen_4092_);
lean_inc(v_ngen_4091_);
lean_inc(v_nextMacroScope_4090_);
lean_inc(v_env_4089_);
lean_dec(v___x_4088_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4150_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4103_; 
v___x_4100_ = l_Lean_Environment_setExporting(v_env_4089_, v_isExporting_4079_);
v___x_4101_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__2);
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 5, v___x_4101_);
lean_ctor_set(v___x_4098_, 0, v___x_4100_);
v___x_4103_ = v___x_4098_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4100_);
lean_ctor_set(v_reuseFailAlloc_4149_, 1, v_nextMacroScope_4090_);
lean_ctor_set(v_reuseFailAlloc_4149_, 2, v_ngen_4091_);
lean_ctor_set(v_reuseFailAlloc_4149_, 3, v_auxDeclNGen_4092_);
lean_ctor_set(v_reuseFailAlloc_4149_, 4, v_traceState_4093_);
lean_ctor_set(v_reuseFailAlloc_4149_, 5, v___x_4101_);
lean_ctor_set(v_reuseFailAlloc_4149_, 6, v_messages_4094_);
lean_ctor_set(v_reuseFailAlloc_4149_, 7, v_infoState_4095_);
lean_ctor_set(v_reuseFailAlloc_4149_, 8, v_snapshotTasks_4096_);
v___x_4103_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v_mctx_4106_; lean_object* v_zetaDeltaFVarIds_4107_; lean_object* v_postponed_4108_; lean_object* v_diag_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4147_; 
v___x_4104_ = lean_st_ref_set(v___y_4083_, v___x_4103_);
v___x_4105_ = lean_st_ref_take(v___y_4081_);
v_mctx_4106_ = lean_ctor_get(v___x_4105_, 0);
v_zetaDeltaFVarIds_4107_ = lean_ctor_get(v___x_4105_, 2);
v_postponed_4108_ = lean_ctor_get(v___x_4105_, 3);
v_diag_4109_ = lean_ctor_get(v___x_4105_, 4);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4147_ == 0)
{
lean_object* v_unused_4148_; 
v_unused_4148_ = lean_ctor_get(v___x_4105_, 1);
lean_dec(v_unused_4148_);
v___x_4111_ = v___x_4105_;
v_isShared_4112_ = v_isSharedCheck_4147_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_diag_4109_);
lean_inc(v_postponed_4108_);
lean_inc(v_zetaDeltaFVarIds_4107_);
lean_inc(v_mctx_4106_);
lean_dec(v___x_4105_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4147_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4113_; lean_object* v___x_4115_; 
v___x_4113_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3, &l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___closed__3);
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 1, v___x_4113_);
v___x_4115_ = v___x_4111_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_mctx_4106_);
lean_ctor_set(v_reuseFailAlloc_4146_, 1, v___x_4113_);
lean_ctor_set(v_reuseFailAlloc_4146_, 2, v_zetaDeltaFVarIds_4107_);
lean_ctor_set(v_reuseFailAlloc_4146_, 3, v_postponed_4108_);
lean_ctor_set(v_reuseFailAlloc_4146_, 4, v_diag_4109_);
v___x_4115_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4116_; lean_object* v_r_4117_; 
v___x_4116_ = lean_st_ref_set(v___y_4081_, v___x_4115_);
lean_inc(v___y_4083_);
lean_inc_ref(v___y_4082_);
lean_inc(v___y_4081_);
lean_inc_ref(v___y_4080_);
v_r_4117_ = lean_apply_5(v_x_4078_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, lean_box(0));
if (lean_obj_tag(v_r_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4134_; 
v_a_4118_ = lean_ctor_get(v_r_4117_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v_r_4117_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4120_ = v_r_4117_;
v_isShared_4121_ = v_isSharedCheck_4134_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v_r_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4134_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
lean_inc(v_a_4118_);
if (v_isShared_4121_ == 0)
{
lean_ctor_set_tag(v___x_4120_, 1);
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
v___x_4124_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4083_, v_isExporting_4087_, v___x_4101_, v___y_4081_, v___x_4113_, v___x_4123_);
lean_dec_ref(v___x_4123_);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4131_ == 0)
{
lean_object* v_unused_4132_; 
v_unused_4132_ = lean_ctor_get(v___x_4124_, 0);
lean_dec(v_unused_4132_);
v___x_4126_ = v___x_4124_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_dec(v___x_4124_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 0, v_a_4118_);
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4118_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
v_a_4135_ = lean_ctor_get(v_r_4117_, 0);
lean_inc(v_a_4135_);
lean_dec_ref(v_r_4117_);
v___x_4136_ = lean_box(0);
v___x_4137_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___lam__0(v___y_4083_, v_isExporting_4087_, v___x_4101_, v___y_4081_, v___x_4113_, v___x_4136_);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; 
v_unused_4145_ = lean_ctor_get(v___x_4137_, 0);
lean_dec(v_unused_4145_);
v___x_4139_ = v___x_4137_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_dec(v___x_4137_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
lean_ctor_set_tag(v___x_4139_, 1);
lean_ctor_set(v___x_4139_, 0, v_a_4135_);
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4135_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg___boxed(lean_object* v_x_4152_, lean_object* v_isExporting_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
uint8_t v_isExporting_boxed_4159_; lean_object* v_res_4160_; 
v_isExporting_boxed_4159_ = lean_unbox(v_isExporting_4153_);
v_res_4160_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4152_, v_isExporting_boxed_4159_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(lean_object* v_00_u03b1_4161_, lean_object* v_x_4162_, uint8_t v_isExporting_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v_x_4162_, v_isExporting_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___boxed(lean_object* v_00_u03b1_4170_, lean_object* v_x_4171_, lean_object* v_isExporting_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
uint8_t v_isExporting_boxed_4178_; lean_object* v_res_4179_; 
v_isExporting_boxed_4178_ = lean_unbox(v_isExporting_4172_);
v_res_4179_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2(v_00_u03b1_4170_, v_x_4171_, v_isExporting_boxed_4178_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(lean_object* v_lctx_4180_, lean_object* v_localInsts_4181_, lean_object* v_x_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v___x_4188_; 
v___x_4188_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_4180_, v_localInsts_4181_, v_x_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4188_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4188_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
else
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
v_a_4197_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4199_ = v___x_4188_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4188_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg___boxed(lean_object* v_lctx_4205_, lean_object* v_localInsts_4206_, lean_object* v_x_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4205_, v_localInsts_4206_, v_x_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(lean_object* v_00_u03b1_4214_, lean_object* v_lctx_4215_, lean_object* v_localInsts_4216_, lean_object* v_x_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v_lctx_4215_, v_localInsts_4216_, v_x_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___boxed(lean_object* v_00_u03b1_4224_, lean_object* v_lctx_4225_, lean_object* v_localInsts_4226_, lean_object* v_x_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4(v_00_u03b1_4224_, v_lctx_4225_, v_localInsts_4226_, v_x_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0(lean_object* v_declName_4234_, lean_object* v_x_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4241_ = l_Lean_MessageData_ofName(v_declName_4234_);
v___x_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed(lean_object* v_declName_4243_, lean_object* v_x_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l_Lean_Meta_mkInjectiveTheorems___lam__0(v_declName_4243_, v_x_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
lean_dec_ref(v_x_4244_);
return v_res_4250_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4251_; 
v___x_4251_ = l_instMonadEIO(lean_box(0));
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(lean_object* v_msg_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v_toApplicative_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4325_; 
v___x_4262_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__0);
v___x_4263_ = l_StateRefT_x27_instMonad___redArg(v___x_4262_);
v_toApplicative_4264_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4325_ == 0)
{
lean_object* v_unused_4326_; 
v_unused_4326_ = lean_ctor_get(v___x_4263_, 1);
lean_dec(v_unused_4326_);
v___x_4266_ = v___x_4263_;
v_isShared_4267_ = v_isSharedCheck_4325_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_toApplicative_4264_);
lean_dec(v___x_4263_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4325_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v_toFunctor_4268_; lean_object* v_toSeq_4269_; lean_object* v_toSeqLeft_4270_; lean_object* v_toSeqRight_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4323_; 
v_toFunctor_4268_ = lean_ctor_get(v_toApplicative_4264_, 0);
v_toSeq_4269_ = lean_ctor_get(v_toApplicative_4264_, 2);
v_toSeqLeft_4270_ = lean_ctor_get(v_toApplicative_4264_, 3);
v_toSeqRight_4271_ = lean_ctor_get(v_toApplicative_4264_, 4);
v_isSharedCheck_4323_ = !lean_is_exclusive(v_toApplicative_4264_);
if (v_isSharedCheck_4323_ == 0)
{
lean_object* v_unused_4324_; 
v_unused_4324_ = lean_ctor_get(v_toApplicative_4264_, 1);
lean_dec(v_unused_4324_);
v___x_4273_ = v_toApplicative_4264_;
v_isShared_4274_ = v_isSharedCheck_4323_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_toSeqRight_4271_);
lean_inc(v_toSeqLeft_4270_);
lean_inc(v_toSeq_4269_);
lean_inc(v_toFunctor_4268_);
lean_dec(v_toApplicative_4264_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4323_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___f_4275_; lean_object* v___f_4276_; lean_object* v___f_4277_; lean_object* v___f_4278_; lean_object* v___x_4279_; lean_object* v___f_4280_; lean_object* v___f_4281_; lean_object* v___f_4282_; lean_object* v___x_4284_; 
v___f_4275_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__1));
v___f_4276_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_4268_);
v___f_4277_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4277_, 0, v_toFunctor_4268_);
v___f_4278_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4278_, 0, v_toFunctor_4268_);
v___x_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___f_4277_);
lean_ctor_set(v___x_4279_, 1, v___f_4278_);
v___f_4280_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4280_, 0, v_toSeqRight_4271_);
v___f_4281_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4281_, 0, v_toSeqLeft_4270_);
v___f_4282_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4282_, 0, v_toSeq_4269_);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 4, v___f_4280_);
lean_ctor_set(v___x_4273_, 3, v___f_4281_);
lean_ctor_set(v___x_4273_, 2, v___f_4282_);
lean_ctor_set(v___x_4273_, 1, v___f_4275_);
lean_ctor_set(v___x_4273_, 0, v___x_4279_);
v___x_4284_ = v___x_4273_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4279_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v___f_4275_);
lean_ctor_set(v_reuseFailAlloc_4322_, 2, v___f_4282_);
lean_ctor_set(v_reuseFailAlloc_4322_, 3, v___f_4281_);
lean_ctor_set(v_reuseFailAlloc_4322_, 4, v___f_4280_);
v___x_4284_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
lean_object* v___x_4286_; 
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 1, v___f_4276_);
lean_ctor_set(v___x_4266_, 0, v___x_4284_);
v___x_4286_ = v___x_4266_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4284_);
lean_ctor_set(v_reuseFailAlloc_4321_, 1, v___f_4276_);
v___x_4286_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
lean_object* v___x_4287_; lean_object* v_toApplicative_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4319_; 
v___x_4287_ = l_StateRefT_x27_instMonad___redArg(v___x_4286_);
v_toApplicative_4288_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4319_ == 0)
{
lean_object* v_unused_4320_; 
v_unused_4320_ = lean_ctor_get(v___x_4287_, 1);
lean_dec(v_unused_4320_);
v___x_4290_ = v___x_4287_;
v_isShared_4291_ = v_isSharedCheck_4319_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_toApplicative_4288_);
lean_dec(v___x_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4319_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v_toFunctor_4292_; lean_object* v_toSeq_4293_; lean_object* v_toSeqLeft_4294_; lean_object* v_toSeqRight_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4317_; 
v_toFunctor_4292_ = lean_ctor_get(v_toApplicative_4288_, 0);
v_toSeq_4293_ = lean_ctor_get(v_toApplicative_4288_, 2);
v_toSeqLeft_4294_ = lean_ctor_get(v_toApplicative_4288_, 3);
v_toSeqRight_4295_ = lean_ctor_get(v_toApplicative_4288_, 4);
v_isSharedCheck_4317_ = !lean_is_exclusive(v_toApplicative_4288_);
if (v_isSharedCheck_4317_ == 0)
{
lean_object* v_unused_4318_; 
v_unused_4318_ = lean_ctor_get(v_toApplicative_4288_, 1);
lean_dec(v_unused_4318_);
v___x_4297_ = v_toApplicative_4288_;
v_isShared_4298_ = v_isSharedCheck_4317_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_toSeqRight_4295_);
lean_inc(v_toSeqLeft_4294_);
lean_inc(v_toSeq_4293_);
lean_inc(v_toFunctor_4292_);
lean_dec(v_toApplicative_4288_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4317_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___f_4299_; lean_object* v___f_4300_; lean_object* v___f_4301_; lean_object* v___f_4302_; lean_object* v___x_4303_; lean_object* v___f_4304_; lean_object* v___f_4305_; lean_object* v___f_4306_; lean_object* v___x_4308_; 
v___f_4299_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__3));
v___f_4300_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_4292_);
v___f_4301_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4301_, 0, v_toFunctor_4292_);
v___f_4302_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4302_, 0, v_toFunctor_4292_);
v___x_4303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4303_, 0, v___f_4301_);
lean_ctor_set(v___x_4303_, 1, v___f_4302_);
v___f_4304_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4304_, 0, v_toSeqRight_4295_);
v___f_4305_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4305_, 0, v_toSeqLeft_4294_);
v___f_4306_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4306_, 0, v_toSeq_4293_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 4, v___f_4304_);
lean_ctor_set(v___x_4297_, 3, v___f_4305_);
lean_ctor_set(v___x_4297_, 2, v___f_4306_);
lean_ctor_set(v___x_4297_, 1, v___f_4299_);
lean_ctor_set(v___x_4297_, 0, v___x_4303_);
v___x_4308_ = v___x_4297_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4303_);
lean_ctor_set(v_reuseFailAlloc_4316_, 1, v___f_4299_);
lean_ctor_set(v_reuseFailAlloc_4316_, 2, v___f_4306_);
lean_ctor_set(v_reuseFailAlloc_4316_, 3, v___f_4305_);
lean_ctor_set(v_reuseFailAlloc_4316_, 4, v___f_4304_);
v___x_4308_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
lean_object* v___x_4310_; 
if (v_isShared_4291_ == 0)
{
lean_ctor_set(v___x_4290_, 1, v___f_4300_);
lean_ctor_set(v___x_4290_, 0, v___x_4308_);
v___x_4310_ = v___x_4290_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4308_);
lean_ctor_set(v_reuseFailAlloc_4315_, 1, v___f_4300_);
v___x_4310_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_18093__overap_4313_; lean_object* v___x_4314_; 
v___x_4311_ = lean_box(0);
v___x_4312_ = l_instInhabitedOfMonad___redArg(v___x_4310_, v___x_4311_);
v___x_18093__overap_4313_ = lean_panic_fn(v___x_4312_, v_msg_4256_);
lean_inc(v___y_4260_);
lean_inc_ref(v___y_4259_);
lean_inc(v___y_4258_);
lean_inc_ref(v___y_4257_);
v___x_4314_ = lean_apply_5(v___x_18093__overap_4313_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, lean_box(0));
return v___x_4314_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1___boxed(lean_object* v_msg_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v_msg_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
return v_res_4333_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__0));
v___x_4336_ = l_Lean_stringToMessageData(v___x_4335_);
return v___x_4336_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4339_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__2));
v___x_4340_ = lean_unsigned_to_nat(11u);
v___x_4341_ = lean_unsigned_to_nat(122u);
v___x_4342_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__3));
v___x_4343_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__2));
v___x_4344_ = l_mkPanicMessageWithDecl(v___x_4343_, v___x_4342_, v___x_4341_, v___x_4340_, v___x_4339_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(lean_object* v_constName_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v___x_4359_; lean_object* v_env_4360_; uint8_t v___x_4361_; lean_object* v___x_4362_; 
v___x_4359_ = lean_st_ref_get(v___y_4349_);
v_env_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc_ref(v_env_4360_);
lean_dec(v___x_4359_);
v___x_4361_ = 0;
lean_inc(v_constName_4345_);
v___x_4362_ = l_Lean_Environment_findAsync_x3f(v_env_4360_, v_constName_4345_, v___x_4361_);
if (lean_obj_tag(v___x_4362_) == 1)
{
lean_object* v_val_4363_; uint8_t v_kind_4364_; 
v_val_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_val_4363_);
lean_dec_ref(v___x_4362_);
v_kind_4364_ = lean_ctor_get_uint8(v_val_4363_, sizeof(void*)*3);
if (v_kind_4364_ == 6)
{
lean_object* v___x_4365_; 
v___x_4365_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4363_);
if (lean_obj_tag(v___x_4365_) == 6)
{
lean_object* v_val_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec(v_constName_4345_);
v_val_4366_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4365_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_val_4366_);
lean_dec(v___x_4365_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
lean_ctor_set_tag(v___x_4368_, 0);
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_val_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
else
{
lean_object* v___x_4374_; lean_object* v___x_4375_; 
lean_dec_ref(v___x_4365_);
v___x_4374_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__4);
v___x_4375_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1_spec__1(v___x_4374_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4384_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4378_ = v___x_4375_;
v_isShared_4379_ = v_isSharedCheck_4384_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4384_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
if (lean_obj_tag(v_a_4376_) == 0)
{
lean_del_object(v___x_4378_);
goto v___jp_4351_;
}
else
{
lean_object* v_val_4380_; lean_object* v___x_4382_; 
lean_dec(v_constName_4345_);
v_val_4380_ = lean_ctor_get(v_a_4376_, 0);
lean_inc(v_val_4380_);
lean_dec_ref(v_a_4376_);
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v_val_4380_);
v___x_4382_ = v___x_4378_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_val_4380_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_dec(v_constName_4345_);
v_a_4385_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4375_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4375_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4385_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
}
else
{
lean_dec(v_val_4363_);
goto v___jp_4351_;
}
}
else
{
lean_dec(v___x_4362_);
goto v___jp_4351_;
}
v___jp_4351_:
{
lean_object* v___x_4352_; uint8_t v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4352_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4353_ = 0;
v___x_4354_ = l_Lean_MessageData_ofConstName(v_constName_4345_, v___x_4353_);
v___x_4355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4352_);
lean_ctor_set(v___x_4355_, 1, v___x_4354_);
v___x_4356_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___closed__1);
v___x_4357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4355_);
lean_ctor_set(v___x_4357_, 1, v___x_4356_);
v___x_4358_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4357_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
return v___x_4358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1___boxed(lean_object* v_constName_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_constName_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(lean_object* v_head_4400_, lean_object* v___x_4401_, lean_object* v___x_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkInjectiveTheorems_spec__1(v_head_4400_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4420_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4411_ = v___x_4408_;
v_isShared_4412_ = v_isSharedCheck_4420_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4408_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4420_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v_numFields_4413_; uint8_t v___x_4414_; 
v_numFields_4413_ = lean_ctor_get(v_a_4409_, 4);
v___x_4414_ = lean_nat_dec_lt(v___x_4401_, v_numFields_4413_);
if (v___x_4414_ == 0)
{
lean_object* v___x_4416_; 
lean_dec(v_a_4409_);
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 0, v___x_4402_);
v___x_4416_ = v___x_4411_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v___x_4402_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
else
{
lean_object* v___x_4418_; 
lean_del_object(v___x_4411_);
lean_inc(v_a_4409_);
v___x_4418_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem(v_a_4409_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v___x_4419_; 
lean_dec_ref(v___x_4418_);
v___x_4419_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheorem(v_a_4409_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
return v___x_4419_;
}
else
{
lean_dec(v_a_4409_);
return v___x_4418_;
}
}
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
v_a_4421_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4408_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4408_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed(lean_object* v_head_4429_, lean_object* v___x_4430_, lean_object* v___x_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0(v_head_4429_, v___x_4430_, v___x_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___x_4430_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(uint8_t v___y_4438_, uint8_t v___x_4439_, lean_object* v_as_x27_4440_, lean_object* v_b_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
if (lean_obj_tag(v_as_x27_4440_) == 0)
{
lean_object* v___x_4447_; 
v___x_4447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4447_, 0, v_b_4441_);
return v___x_4447_;
}
else
{
lean_object* v_head_4448_; lean_object* v_tail_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___f_4452_; uint8_t v___y_4454_; uint8_t v___x_4457_; 
v_head_4448_ = lean_ctor_get(v_as_x27_4440_, 0);
lean_inc(v_head_4448_);
v_tail_4449_ = lean_ctor_get(v_as_x27_4440_, 1);
lean_inc(v_tail_4449_);
lean_dec_ref(v_as_x27_4440_);
v___x_4450_ = lean_unsigned_to_nat(0u);
v___x_4451_ = lean_box(0);
lean_inc(v_head_4448_);
v___f_4452_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4452_, 0, v_head_4448_);
lean_closure_set(v___f_4452_, 1, v___x_4450_);
lean_closure_set(v___f_4452_, 2, v___x_4451_);
v___x_4457_ = l_Lean_isPrivateName(v_head_4448_);
lean_dec(v_head_4448_);
if (v___x_4457_ == 0)
{
v___y_4454_ = v___y_4438_;
goto v___jp_4453_;
}
else
{
v___y_4454_ = v___x_4439_;
goto v___jp_4453_;
}
v___jp_4453_:
{
lean_object* v___x_4455_; 
v___x_4455_ = l_Lean_withExporting___at___00Lean_Meta_mkInjectiveTheorems_spec__2___redArg(v___f_4452_, v___y_4454_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_dec_ref(v___x_4455_);
v_as_x27_4440_ = v_tail_4449_;
v_b_4441_ = v___x_4451_;
goto _start;
}
else
{
lean_dec(v_tail_4449_);
return v___x_4455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg___boxed(lean_object* v___y_4458_, lean_object* v___x_4459_, lean_object* v_as_x27_4460_, lean_object* v_b_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_){
_start:
{
uint8_t v___y_19026__boxed_4467_; uint8_t v___x_19027__boxed_4468_; lean_object* v_res_4469_; 
v___y_19026__boxed_4467_ = lean_unbox(v___y_4458_);
v___x_19027__boxed_4468_ = lean_unbox(v___x_4459_);
v_res_4469_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_19026__boxed_4467_, v___x_19027__boxed_4468_, v_as_x27_4460_, v_b_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4462_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1(uint8_t v___y_4470_, uint8_t v_hasTrace_4471_, lean_object* v_ctors_4472_, lean_object* v___x_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4470_, v_hasTrace_4471_, v_ctors_4472_, v___x_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4486_; 
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4486_ == 0)
{
lean_object* v_unused_4487_; 
v_unused_4487_ = lean_ctor_get(v___x_4479_, 0);
lean_dec(v_unused_4487_);
v___x_4481_ = v___x_4479_;
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
else
{
lean_dec(v___x_4479_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4484_; 
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 0, v___x_4473_);
v___x_4484_ = v___x_4481_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4473_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
else
{
return v___x_4479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed(lean_object* v___y_4488_, lean_object* v_hasTrace_4489_, lean_object* v_ctors_4490_, lean_object* v___x_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
uint8_t v___y_19071__boxed_4497_; uint8_t v_hasTrace_boxed_4498_; lean_object* v_res_4499_; 
v___y_19071__boxed_4497_ = lean_unbox(v___y_4488_);
v_hasTrace_boxed_4498_ = lean_unbox(v_hasTrace_4489_);
v_res_4499_ = l_Lean_Meta_mkInjectiveTheorems___lam__1(v___y_19071__boxed_4497_, v_hasTrace_boxed_4498_, v_ctors_4490_, v___x_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2(uint8_t v_hasTrace_4500_, uint8_t v___x_4501_, lean_object* v_ctors_4502_, lean_object* v___x_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v_hasTrace_4500_, v___x_4501_, v_ctors_4502_, v___x_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed(lean_object* v_hasTrace_4518_, lean_object* v___x_4519_, lean_object* v_ctors_4520_, lean_object* v___x_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
uint8_t v_hasTrace_boxed_4527_; uint8_t v___x_19112__boxed_4528_; lean_object* v_res_4529_; 
v_hasTrace_boxed_4527_ = lean_unbox(v_hasTrace_4518_);
v___x_19112__boxed_4528_ = lean_unbox(v___x_4519_);
v_res_4529_ = l_Lean_Meta_mkInjectiveTheorems___lam__2(v_hasTrace_boxed_4527_, v___x_19112__boxed_4528_, v_ctors_4520_, v___x_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3(uint8_t v___x_4530_, uint8_t v_isUnsafe_4531_, lean_object* v_ctors_4532_, lean_object* v___x_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
lean_object* v___x_4539_; 
v___x_4539_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___x_4530_, v_isUnsafe_4531_, v_ctors_4532_, v___x_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4546_; 
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4546_ == 0)
{
lean_object* v_unused_4547_; 
v_unused_4547_ = lean_ctor_get(v___x_4539_, 0);
lean_dec(v_unused_4547_);
v___x_4541_ = v___x_4539_;
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
else
{
lean_dec(v___x_4539_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4544_; 
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v___x_4533_);
v___x_4544_ = v___x_4541_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4533_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
else
{
return v___x_4539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed(lean_object* v___x_4548_, lean_object* v_isUnsafe_4549_, lean_object* v_ctors_4550_, lean_object* v___x_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
uint8_t v___x_19153__boxed_4557_; uint8_t v_isUnsafe_boxed_4558_; lean_object* v_res_4559_; 
v___x_19153__boxed_4557_ = lean_unbox(v___x_4548_);
v_isUnsafe_boxed_4558_ = lean_unbox(v_isUnsafe_4549_);
v_res_4559_ = l_Lean_Meta_mkInjectiveTheorems___lam__3(v___x_19153__boxed_4557_, v_isUnsafe_boxed_4558_, v_ctors_4550_, v___x_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
return v_res_4559_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4561_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__0));
v___x_4562_ = l_Lean_stringToMessageData(v___x_4561_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(lean_object* v_constName_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
lean_object* v___x_4569_; lean_object* v_env_4570_; lean_object* v___x_4571_; 
v___x_4569_ = lean_st_ref_get(v___y_4567_);
v_env_4570_ = lean_ctor_get(v___x_4569_, 0);
lean_inc_ref(v_env_4570_);
lean_dec(v___x_4569_);
lean_inc(v_constName_4563_);
v___x_4571_ = l_Lean_isInductiveCore_x3f(v_env_4570_, v_constName_4563_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v___x_4572_; uint8_t v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4572_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_4573_ = 0;
v___x_4574_ = l_Lean_MessageData_ofConstName(v_constName_4563_, v___x_4573_);
v___x_4575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4572_);
lean_ctor_set(v___x_4575_, 1, v___x_4574_);
v___x_4576_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___closed__1);
v___x_4577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4575_);
lean_ctor_set(v___x_4577_, 1, v___x_4576_);
v___x_4578_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_4577_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_);
return v___x_4578_;
}
else
{
lean_object* v_val_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec(v_constName_4563_);
v_val_4579_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4571_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_val_4579_);
lean_dec(v___x_4571_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
lean_ctor_set_tag(v___x_4581_, 0);
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_val_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0___boxed(lean_object* v_constName_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_constName_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
return v_res_4593_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__0(void){
_start:
{
lean_object* v___x_4594_; 
v___x_4594_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4594_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__1(void){
_start:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__0, &l_Lean_Meta_mkInjectiveTheorems___closed__0_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__0);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
return v___x_4596_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__2(void){
_start:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4597_ = lean_unsigned_to_nat(32u);
v___x_4598_ = lean_mk_empty_array_with_capacity(v___x_4597_);
v___x_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
return v___x_4599_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__3(void){
_start:
{
size_t v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4600_ = ((size_t)5ULL);
v___x_4601_ = lean_unsigned_to_nat(0u);
v___x_4602_ = lean_unsigned_to_nat(32u);
v___x_4603_ = lean_mk_empty_array_with_capacity(v___x_4602_);
v___x_4604_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__2, &l_Lean_Meta_mkInjectiveTheorems___closed__2_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__2);
v___x_4605_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4605_, 0, v___x_4604_);
lean_ctor_set(v___x_4605_, 1, v___x_4603_);
lean_ctor_set(v___x_4605_, 2, v___x_4601_);
lean_ctor_set(v___x_4605_, 3, v___x_4601_);
lean_ctor_set_usize(v___x_4605_, 4, v___x_4600_);
return v___x_4605_;
}
}
static lean_object* _init_l_Lean_Meta_mkInjectiveTheorems___closed__4(void){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4606_ = lean_box(1);
v___x_4607_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4608_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_4609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4609_, 0, v___x_4608_);
lean_ctor_set(v___x_4609_, 1, v___x_4607_);
lean_ctor_set(v___x_4609_, 2, v___x_4606_);
return v___x_4609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object* v_declName_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4618_ = lean_st_ref_get(v_a_4616_);
lean_inc(v_declName_4612_);
v___x_4619_ = l_Lean_Meta_isInductivePredicate(v_declName_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4818_; 
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4622_ = v___x_4619_;
v_isShared_4623_ = v_isSharedCheck_4818_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4619_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4818_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v_env_4629_; lean_object* v___f_4630_; lean_object* v___x_4631_; uint8_t v___x_4632_; lean_object* v___y_4634_; lean_object* v___y_4635_; lean_object* v___y_4636_; lean_object* v___y_4637_; uint8_t v___y_4638_; lean_object* v___y_4639_; lean_object* v_a_4640_; lean_object* v___y_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; uint8_t v___y_4654_; lean_object* v___y_4655_; lean_object* v_a_4656_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; uint8_t v___y_4663_; lean_object* v___y_4664_; lean_object* v_a_4665_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; lean_object* v___y_4671_; uint8_t v___y_4672_; lean_object* v___y_4673_; lean_object* v_a_4674_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4689_; lean_object* v___y_4690_; uint8_t v___y_4691_; lean_object* v___y_4692_; lean_object* v_a_4693_; lean_object* v___y_4696_; lean_object* v___y_4697_; lean_object* v___y_4698_; lean_object* v___y_4699_; uint8_t v___y_4700_; lean_object* v___y_4701_; lean_object* v_a_4702_; uint8_t v___y_4705_; uint8_t v___y_4706_; lean_object* v___y_4707_; lean_object* v___y_4708_; lean_object* v___y_4709_; uint8_t v___y_4747_; uint8_t v___x_4814_; 
v_env_4629_ = lean_ctor_get(v___x_4618_, 0);
lean_inc_ref(v_env_4629_);
lean_dec(v___x_4618_);
lean_inc(v_declName_4612_);
v___f_4630_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4630_, 0, v_declName_4612_);
v___x_4631_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveEqTheoremValue___lam__0___closed__2));
v___x_4632_ = 1;
v___x_4814_ = l_Lean_Environment_contains(v_env_4629_, v___x_4631_, v___x_4632_);
if (v___x_4814_ == 0)
{
v___y_4747_ = v___x_4814_;
goto v___jp_4746_;
}
else
{
lean_object* v_options_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; 
v_options_4815_ = lean_ctor_get(v_a_4615_, 2);
v___x_4816_ = l_Lean_Meta_genInjectivity;
v___x_4817_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4815_, v___x_4816_);
v___y_4747_ = v___x_4817_;
goto v___jp_4746_;
}
v___jp_4624_:
{
lean_object* v___x_4625_; lean_object* v___x_4627_; 
v___x_4625_ = lean_box(0);
if (v_isShared_4623_ == 0)
{
lean_ctor_set(v___x_4622_, 0, v___x_4625_);
v___x_4627_ = v___x_4622_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4625_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
v___jp_4633_:
{
lean_object* v___x_4641_; double v___x_4642_; double v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4641_ = lean_io_get_num_heartbeats();
v___x_4642_ = lean_float_of_nat(v___y_4637_);
v___x_4643_ = lean_float_of_nat(v___x_4641_);
v___x_4644_ = lean_box_float(v___x_4642_);
v___x_4645_ = lean_box_float(v___x_4643_);
v___x_4646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4644_);
lean_ctor_set(v___x_4646_, 1, v___x_4645_);
v___x_4647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4647_, 0, v_a_4640_);
lean_ctor_set(v___x_4647_, 1, v___x_4646_);
v___x_4648_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4635_, v___x_4632_, v___y_4636_, v___y_4639_, v___y_4638_, v___y_4634_, v___f_4630_, v___x_4647_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
return v___x_4648_;
}
v___jp_4649_:
{
lean_object* v___x_4657_; 
v___x_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4657_, 0, v_a_4656_);
v___y_4634_ = v___y_4650_;
v___y_4635_ = v___y_4651_;
v___y_4636_ = v___y_4652_;
v___y_4637_ = v___y_4653_;
v___y_4638_ = v___y_4654_;
v___y_4639_ = v___y_4655_;
v_a_4640_ = v___x_4657_;
goto v___jp_4633_;
}
v___jp_4658_:
{
lean_object* v___x_4666_; 
v___x_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4666_, 0, v_a_4665_);
v___y_4634_ = v___y_4659_;
v___y_4635_ = v___y_4660_;
v___y_4636_ = v___y_4661_;
v___y_4637_ = v___y_4662_;
v___y_4638_ = v___y_4663_;
v___y_4639_ = v___y_4664_;
v_a_4640_ = v___x_4666_;
goto v___jp_4633_;
}
v___jp_4667_:
{
lean_object* v___x_4675_; double v___x_4676_; double v___x_4677_; double v___x_4678_; double v___x_4679_; double v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4675_ = lean_io_mono_nanos_now();
v___x_4676_ = lean_float_of_nat(v___y_4671_);
v___x_4677_ = lean_float_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem___closed__2);
v___x_4678_ = lean_float_div(v___x_4676_, v___x_4677_);
v___x_4679_ = lean_float_of_nat(v___x_4675_);
v___x_4680_ = lean_float_div(v___x_4679_, v___x_4677_);
v___x_4681_ = lean_box_float(v___x_4678_);
v___x_4682_ = lean_box_float(v___x_4680_);
v___x_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4681_);
lean_ctor_set(v___x_4683_, 1, v___x_4682_);
v___x_4684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4684_, 0, v_a_4674_);
lean_ctor_set(v___x_4684_, 1, v___x_4683_);
v___x_4685_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__3(v___y_4669_, v___x_4632_, v___y_4670_, v___y_4673_, v___y_4672_, v___y_4668_, v___f_4630_, v___x_4684_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
return v___x_4685_;
}
v___jp_4686_:
{
lean_object* v___x_4694_; 
v___x_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4694_, 0, v_a_4693_);
v___y_4668_ = v___y_4687_;
v___y_4669_ = v___y_4688_;
v___y_4670_ = v___y_4689_;
v___y_4671_ = v___y_4690_;
v___y_4672_ = v___y_4691_;
v___y_4673_ = v___y_4692_;
v_a_4674_ = v___x_4694_;
goto v___jp_4667_;
}
v___jp_4695_:
{
lean_object* v___x_4703_; 
v___x_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4703_, 0, v_a_4702_);
v___y_4668_ = v___y_4696_;
v___y_4669_ = v___y_4697_;
v___y_4670_ = v___y_4698_;
v___y_4671_ = v___y_4699_;
v___y_4672_ = v___y_4700_;
v___y_4673_ = v___y_4701_;
v_a_4674_ = v___x_4703_;
goto v___jp_4667_;
}
v___jp_4704_:
{
lean_object* v___x_4710_; lean_object* v_a_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
v___x_4710_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__1___redArg(v_a_4616_);
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
lean_inc(v_a_4711_);
lean_dec_ref(v___x_4710_);
v___x_4712_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4713_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v___y_4709_, v___x_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4714_ = lean_io_mono_nanos_now();
v___x_4715_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_object* v_a_4716_; uint8_t v_isUnsafe_4717_; 
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_a_4716_);
lean_dec_ref(v___x_4715_);
v_isUnsafe_4717_ = lean_ctor_get_uint8(v_a_4716_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4717_ == 0)
{
lean_object* v_ctors_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___f_4724_; lean_object* v___x_4725_; 
v_ctors_4718_ = lean_ctor_get(v_a_4716_, 4);
lean_inc(v_ctors_4718_);
lean_dec(v_a_4716_);
v___x_4719_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4720_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4721_ = lean_box(0);
v___x_4722_ = lean_box(v___y_4706_);
v___x_4723_ = lean_box(v___x_4713_);
v___f_4724_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4724_, 0, v___x_4722_);
lean_closure_set(v___f_4724_, 1, v___x_4723_);
lean_closure_set(v___f_4724_, 2, v_ctors_4718_);
lean_closure_set(v___f_4724_, 3, v___x_4721_);
v___x_4725_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4719_, v___x_4720_, v___f_4724_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
if (lean_obj_tag(v___x_4725_) == 0)
{
lean_object* v_a_4726_; 
v_a_4726_ = lean_ctor_get(v___x_4725_, 0);
lean_inc(v_a_4726_);
lean_dec_ref(v___x_4725_);
v___y_4687_ = v_a_4711_;
v___y_4688_ = v___y_4707_;
v___y_4689_ = v___y_4708_;
v___y_4690_ = v___x_4714_;
v___y_4691_ = v___y_4705_;
v___y_4692_ = v___y_4709_;
v_a_4693_ = v_a_4726_;
goto v___jp_4686_;
}
else
{
lean_object* v_a_4727_; 
v_a_4727_ = lean_ctor_get(v___x_4725_, 0);
lean_inc(v_a_4727_);
lean_dec_ref(v___x_4725_);
v___y_4696_ = v_a_4711_;
v___y_4697_ = v___y_4707_;
v___y_4698_ = v___y_4708_;
v___y_4699_ = v___x_4714_;
v___y_4700_ = v___y_4705_;
v___y_4701_ = v___y_4709_;
v_a_4702_ = v_a_4727_;
goto v___jp_4695_;
}
}
else
{
lean_object* v___x_4728_; 
lean_dec(v_a_4716_);
v___x_4728_ = lean_box(0);
v___y_4687_ = v_a_4711_;
v___y_4688_ = v___y_4707_;
v___y_4689_ = v___y_4708_;
v___y_4690_ = v___x_4714_;
v___y_4691_ = v___y_4705_;
v___y_4692_ = v___y_4709_;
v_a_4693_ = v___x_4728_;
goto v___jp_4686_;
}
}
else
{
lean_object* v_a_4729_; 
v_a_4729_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_a_4729_);
lean_dec_ref(v___x_4715_);
v___y_4696_ = v_a_4711_;
v___y_4697_ = v___y_4707_;
v___y_4698_ = v___y_4708_;
v___y_4699_ = v___x_4714_;
v___y_4700_ = v___y_4705_;
v___y_4701_ = v___y_4709_;
v_a_4702_ = v_a_4729_;
goto v___jp_4695_;
}
}
else
{
lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4730_ = lean_io_get_num_heartbeats();
v___x_4731_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; uint8_t v_isUnsafe_4733_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_a_4732_);
lean_dec_ref(v___x_4731_);
v_isUnsafe_4733_ = lean_ctor_get_uint8(v_a_4732_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4733_ == 0)
{
lean_object* v_ctors_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___f_4740_; lean_object* v___x_4741_; 
v_ctors_4734_ = lean_ctor_get(v_a_4732_, 4);
lean_inc(v_ctors_4734_);
lean_dec(v_a_4732_);
v___x_4735_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4736_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4737_ = lean_box(0);
v___x_4738_ = lean_box(v___x_4713_);
v___x_4739_ = lean_box(v_isUnsafe_4733_);
v___f_4740_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__3___boxed), 9, 4);
lean_closure_set(v___f_4740_, 0, v___x_4738_);
lean_closure_set(v___f_4740_, 1, v___x_4739_);
lean_closure_set(v___f_4740_, 2, v_ctors_4734_);
lean_closure_set(v___f_4740_, 3, v___x_4737_);
v___x_4741_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4735_, v___x_4736_, v___f_4740_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_a_4742_; 
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
lean_inc(v_a_4742_);
lean_dec_ref(v___x_4741_);
v___y_4650_ = v_a_4711_;
v___y_4651_ = v___y_4707_;
v___y_4652_ = v___y_4708_;
v___y_4653_ = v___x_4730_;
v___y_4654_ = v___y_4705_;
v___y_4655_ = v___y_4709_;
v_a_4656_ = v_a_4742_;
goto v___jp_4649_;
}
else
{
lean_object* v_a_4743_; 
v_a_4743_ = lean_ctor_get(v___x_4741_, 0);
lean_inc(v_a_4743_);
lean_dec_ref(v___x_4741_);
v___y_4659_ = v_a_4711_;
v___y_4660_ = v___y_4707_;
v___y_4661_ = v___y_4708_;
v___y_4662_ = v___x_4730_;
v___y_4663_ = v___y_4705_;
v___y_4664_ = v___y_4709_;
v_a_4665_ = v_a_4743_;
goto v___jp_4658_;
}
}
else
{
lean_object* v___x_4744_; 
lean_dec(v_a_4732_);
v___x_4744_ = lean_box(0);
v___y_4650_ = v_a_4711_;
v___y_4651_ = v___y_4707_;
v___y_4652_ = v___y_4708_;
v___y_4653_ = v___x_4730_;
v___y_4654_ = v___y_4705_;
v___y_4655_ = v___y_4709_;
v_a_4656_ = v___x_4744_;
goto v___jp_4649_;
}
}
else
{
lean_object* v_a_4745_; 
v_a_4745_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_a_4745_);
lean_dec_ref(v___x_4731_);
v___y_4659_ = v_a_4711_;
v___y_4660_ = v___y_4707_;
v___y_4661_ = v___y_4708_;
v___y_4662_ = v___x_4730_;
v___y_4663_ = v___y_4705_;
v___y_4664_ = v___y_4709_;
v_a_4665_ = v_a_4745_;
goto v___jp_4658_;
}
}
}
v___jp_4746_:
{
if (v___y_4747_ == 0)
{
lean_dec_ref(v___f_4630_);
lean_dec(v_a_4620_);
lean_dec(v_declName_4612_);
goto v___jp_4624_;
}
else
{
uint8_t v___x_4748_; 
v___x_4748_ = lean_unbox(v_a_4620_);
lean_dec(v_a_4620_);
if (v___x_4748_ == 0)
{
lean_object* v_options_4749_; uint8_t v_hasTrace_4750_; 
lean_del_object(v___x_4622_);
v_options_4749_ = lean_ctor_get(v_a_4615_, 2);
v_hasTrace_4750_ = lean_ctor_get_uint8(v_options_4749_, sizeof(void*)*1);
if (v_hasTrace_4750_ == 0)
{
lean_object* v___x_4751_; 
lean_dec_ref(v___f_4630_);
v___x_4751_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
if (lean_obj_tag(v___x_4751_) == 0)
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4769_; 
v_a_4752_ = lean_ctor_get(v___x_4751_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4754_ = v___x_4751_;
v_isShared_4755_ = v_isSharedCheck_4769_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4751_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4769_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
uint8_t v_isUnsafe_4756_; 
v_isUnsafe_4756_ = lean_ctor_get_uint8(v_a_4752_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4756_ == 0)
{
lean_object* v_ctors_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___f_4763_; lean_object* v___x_4764_; 
lean_del_object(v___x_4754_);
v_ctors_4757_ = lean_ctor_get(v_a_4752_, 4);
lean_inc(v_ctors_4757_);
lean_dec(v_a_4752_);
v___x_4758_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4759_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4760_ = lean_box(0);
v___x_4761_ = lean_box(v___y_4747_);
v___x_4762_ = lean_box(v_hasTrace_4750_);
v___f_4763_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__1___boxed), 9, 4);
lean_closure_set(v___f_4763_, 0, v___x_4761_);
lean_closure_set(v___f_4763_, 1, v___x_4762_);
lean_closure_set(v___f_4763_, 2, v_ctors_4757_);
lean_closure_set(v___f_4763_, 3, v___x_4760_);
v___x_4764_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4758_, v___x_4759_, v___f_4763_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
return v___x_4764_;
}
else
{
lean_object* v___x_4765_; lean_object* v___x_4767_; 
lean_dec(v_a_4752_);
v___x_4765_ = lean_box(0);
if (v_isShared_4755_ == 0)
{
lean_ctor_set(v___x_4754_, 0, v___x_4765_);
v___x_4767_ = v___x_4754_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4765_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
}
else
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4777_; 
v_a_4770_ = lean_ctor_get(v___x_4751_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4772_ = v___x_4751_;
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4751_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4775_; 
if (v_isShared_4773_ == 0)
{
v___x_4775_ = v___x_4772_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_a_4770_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
else
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v_a_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; 
v___x_4778_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4779_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__1___redArg(v___x_4778_, v_a_4615_);
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc(v_a_4780_);
lean_dec_ref(v___x_4779_);
v___x_4781_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq_spec__2___closed__1));
v___x_4782_ = lean_unbox(v_a_4780_);
if (v___x_4782_ == 0)
{
lean_object* v___x_4783_; uint8_t v___x_4784_; 
v___x_4783_ = l_Lean_trace_profiler;
v___x_4784_ = l_Lean_Option_get___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__2(v_options_4749_, v___x_4783_);
if (v___x_4784_ == 0)
{
lean_object* v___x_4785_; 
lean_dec(v_a_4780_);
lean_dec_ref(v___f_4630_);
v___x_4785_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkInjectiveTheorems_spec__0(v_declName_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4803_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4788_ = v___x_4785_;
v_isShared_4789_ = v_isSharedCheck_4803_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4785_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4803_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
uint8_t v_isUnsafe_4790_; 
v_isUnsafe_4790_ = lean_ctor_get_uint8(v_a_4786_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4790_ == 0)
{
lean_object* v_ctors_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___f_4797_; lean_object* v___x_4798_; 
lean_del_object(v___x_4788_);
v_ctors_4791_ = lean_ctor_get(v_a_4786_, 4);
lean_inc(v_ctors_4791_);
lean_dec(v_a_4786_);
v___x_4792_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_4793_ = ((lean_object*)(l_Lean_Meta_mkInjectiveTheorems___closed__5));
v___x_4794_ = lean_box(0);
v___x_4795_ = lean_box(v_hasTrace_4750_);
v___x_4796_ = lean_box(v___x_4784_);
v___f_4797_ = lean_alloc_closure((void*)(l_Lean_Meta_mkInjectiveTheorems___lam__2___boxed), 9, 4);
lean_closure_set(v___f_4797_, 0, v___x_4795_);
lean_closure_set(v___f_4797_, 1, v___x_4796_);
lean_closure_set(v___f_4797_, 2, v_ctors_4791_);
lean_closure_set(v___f_4797_, 3, v___x_4794_);
v___x_4798_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkInjectiveTheorems_spec__4___redArg(v___x_4792_, v___x_4793_, v___f_4797_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
return v___x_4798_;
}
else
{
lean_object* v___x_4799_; lean_object* v___x_4801_; 
lean_dec(v_a_4786_);
v___x_4799_ = lean_box(0);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 0, v___x_4799_);
v___x_4801_ = v___x_4788_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v___x_4799_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
}
else
{
lean_object* v_a_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4811_; 
v_a_4804_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4806_ = v___x_4785_;
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_a_4804_);
lean_dec(v___x_4785_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4809_; 
if (v_isShared_4807_ == 0)
{
v___x_4809_ = v___x_4806_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v_a_4804_);
v___x_4809_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
return v___x_4809_;
}
}
}
}
else
{
uint8_t v___x_4812_; 
v___x_4812_ = lean_unbox(v_a_4780_);
lean_dec(v_a_4780_);
v___y_4705_ = v___x_4812_;
v___y_4706_ = v_hasTrace_4750_;
v___y_4707_ = v___x_4778_;
v___y_4708_ = v___x_4781_;
v___y_4709_ = v_options_4749_;
goto v___jp_4704_;
}
}
else
{
uint8_t v___x_4813_; 
v___x_4813_ = lean_unbox(v_a_4780_);
lean_dec(v_a_4780_);
v___y_4705_ = v___x_4813_;
v___y_4706_ = v_hasTrace_4750_;
v___y_4707_ = v___x_4778_;
v___y_4708_ = v___x_4781_;
v___y_4709_ = v_options_4749_;
goto v___jp_4704_;
}
}
}
else
{
lean_dec_ref(v___f_4630_);
lean_dec(v_declName_4612_);
goto v___jp_4624_;
}
}
}
}
}
else
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
lean_dec(v___x_4618_);
lean_dec(v_declName_4612_);
v_a_4819_ = lean_ctor_get(v___x_4619_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4619_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4821_ = v___x_4619_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4619_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkInjectiveTheorems___boxed(lean_object* v_declName_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_Lean_Meta_mkInjectiveTheorems(v_declName_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
lean_dec(v_a_4831_);
lean_dec_ref(v_a_4830_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(uint8_t v___y_4834_, uint8_t v___x_4835_, lean_object* v_as_4836_, lean_object* v_as_x27_4837_, lean_object* v_b_4838_, lean_object* v_a_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_){
_start:
{
lean_object* v___x_4845_; 
v___x_4845_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___redArg(v___y_4834_, v___x_4835_, v_as_x27_4837_, v_b_4838_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3___boxed(lean_object* v___y_4846_, lean_object* v___x_4847_, lean_object* v_as_4848_, lean_object* v_as_x27_4849_, lean_object* v_b_4850_, lean_object* v_a_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_){
_start:
{
uint8_t v___y_19783__boxed_4857_; uint8_t v___x_19784__boxed_4858_; lean_object* v_res_4859_; 
v___y_19783__boxed_4857_ = lean_unbox(v___y_4846_);
v___x_19784__boxed_4858_ = lean_unbox(v___x_4847_);
v_res_4859_ = l_List_forIn_x27_loop___at___00Lean_Meta_mkInjectiveTheorems_spec__3(v___y_19783__boxed_4857_, v___x_19784__boxed_4858_, v_as_4848_, v_as_x27_4849_, v_b_4850_, v_a_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
lean_dec(v___y_4853_);
lean_dec_ref(v___y_4852_);
lean_dec(v_as_4848_);
return v_res_4859_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4900_ = lean_unsigned_to_nat(4172903888u);
v___x_4901_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4902_ = l_Lean_Name_num___override(v___x_4901_, v___x_4900_);
return v___x_4902_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4904_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4905_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4906_ = l_Lean_Name_str___override(v___x_4905_, v___x_4904_);
return v___x_4906_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4908_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_));
v___x_4909_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4910_ = l_Lean_Name_str___override(v___x_4909_, v___x_4908_);
return v___x_4910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4911_ = lean_unsigned_to_nat(2u);
v___x_4912_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4913_ = l_Lean_Name_num___override(v___x_4912_, v___x_4911_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4915_; uint8_t v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4915_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_solveEqOfCtorEq___closed__6));
v___x_4916_ = 0;
v___x_4917_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_);
v___x_4918_ = l_Lean_registerTraceClass(v___x_4915_, v___x_4916_, v___x_4917_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2____boxed(lean_object* v_a_4919_){
_start:
{
lean_object* v_res_4920_; 
v_res_4920_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_4172903888____hygCtx___hyg_2_();
return v_res_4920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(lean_object* v_a_4921_, lean_object* v_b_4922_){
_start:
{
lean_object* v_array_4923_; lean_object* v_start_4924_; lean_object* v_stop_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4938_; 
v_array_4923_ = lean_ctor_get(v_a_4921_, 0);
v_start_4924_ = lean_ctor_get(v_a_4921_, 1);
v_stop_4925_ = lean_ctor_get(v_a_4921_, 2);
v_isSharedCheck_4938_ = !lean_is_exclusive(v_a_4921_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4927_ = v_a_4921_;
v_isShared_4928_ = v_isSharedCheck_4938_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_stop_4925_);
lean_inc(v_start_4924_);
lean_inc(v_array_4923_);
lean_dec(v_a_4921_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4938_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
uint8_t v___x_4929_; 
v___x_4929_ = lean_nat_dec_lt(v_start_4924_, v_stop_4925_);
if (v___x_4929_ == 0)
{
lean_del_object(v___x_4927_);
lean_dec(v_stop_4925_);
lean_dec(v_start_4924_);
lean_dec_ref(v_array_4923_);
return v_b_4922_;
}
else
{
lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4933_; 
v___x_4930_ = lean_unsigned_to_nat(1u);
v___x_4931_ = lean_nat_add(v_start_4924_, v___x_4930_);
lean_inc_ref(v_array_4923_);
if (v_isShared_4928_ == 0)
{
lean_ctor_set(v___x_4927_, 1, v___x_4931_);
v___x_4933_ = v___x_4927_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_array_4923_);
lean_ctor_set(v_reuseFailAlloc_4937_, 1, v___x_4931_);
lean_ctor_set(v_reuseFailAlloc_4937_, 2, v_stop_4925_);
v___x_4933_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; 
v___x_4934_ = lean_array_fget(v_array_4923_, v_start_4924_);
lean_dec(v_start_4924_);
lean_dec_ref(v_array_4923_);
v___x_4935_ = lean_array_push(v_b_4922_, v___x_4934_);
v_a_4921_ = v___x_4933_;
v_b_4922_ = v___x_4935_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4939_; 
v___x_4939_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4939_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
v___x_4941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4940_);
return v___x_4941_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4942_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4943_ = lean_unsigned_to_nat(0u);
v___x_4944_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4943_);
lean_ctor_set(v___x_4944_, 1, v___x_4943_);
lean_ctor_set(v___x_4944_, 2, v___x_4943_);
lean_ctor_set(v___x_4944_, 3, v___x_4942_);
lean_ctor_set(v___x_4944_, 4, v___x_4942_);
lean_ctor_set(v___x_4944_, 5, v___x_4942_);
lean_ctor_set(v___x_4944_, 6, v___x_4942_);
lean_ctor_set(v___x_4944_, 7, v___x_4942_);
lean_ctor_set(v___x_4944_, 8, v___x_4942_);
return v___x_4944_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4945_ = lean_box(1);
v___x_4946_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_4947_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_4948_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4947_);
lean_ctor_set(v___x_4948_, 1, v___x_4946_);
lean_ctor_set(v___x_4948_, 2, v___x_4945_);
return v___x_4948_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; 
v___x_4950_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_4951_ = l_Lean_stringToMessageData(v___x_4950_);
return v___x_4951_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4953_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_4954_ = l_Lean_stringToMessageData(v___x_4953_);
return v___x_4954_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; 
v___x_4956_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_4957_ = l_Lean_stringToMessageData(v___x_4956_);
return v___x_4957_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_4959_; lean_object* v___x_4960_; 
v___x_4959_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_4960_ = l_Lean_stringToMessageData(v___x_4959_);
return v___x_4960_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4962_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_4963_ = l_Lean_stringToMessageData(v___x_4962_);
return v___x_4963_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15(void){
_start:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4965_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14));
v___x_4966_ = l_Lean_stringToMessageData(v___x_4965_);
return v___x_4966_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17(void){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4968_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16));
v___x_4969_ = l_Lean_stringToMessageData(v___x_4968_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_4970_, lean_object* v_declHint_4971_, lean_object* v___y_4972_){
_start:
{
lean_object* v___x_4974_; lean_object* v_env_4975_; uint8_t v___x_4976_; 
v___x_4974_ = lean_st_ref_get(v___y_4972_);
v_env_4975_ = lean_ctor_get(v___x_4974_, 0);
lean_inc_ref(v_env_4975_);
lean_dec(v___x_4974_);
v___x_4976_ = l_Lean_Name_isAnonymous(v_declHint_4971_);
if (v___x_4976_ == 0)
{
uint8_t v_isExporting_4977_; 
v_isExporting_4977_ = lean_ctor_get_uint8(v_env_4975_, sizeof(void*)*8);
if (v_isExporting_4977_ == 0)
{
lean_object* v___x_4978_; 
lean_dec_ref(v_env_4975_);
lean_dec(v_declHint_4971_);
v___x_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4978_, 0, v_msg_4970_);
return v___x_4978_;
}
else
{
lean_object* v___x_4979_; uint8_t v___x_4980_; 
lean_inc_ref(v_env_4975_);
v___x_4979_ = l_Lean_Environment_setExporting(v_env_4975_, v___x_4976_);
lean_inc(v_declHint_4971_);
lean_inc_ref(v___x_4979_);
v___x_4980_ = l_Lean_Environment_contains(v___x_4979_, v_declHint_4971_, v_isExporting_4977_);
if (v___x_4980_ == 0)
{
lean_object* v___x_4981_; 
lean_dec_ref(v___x_4979_);
lean_dec_ref(v_env_4975_);
lean_dec(v_declHint_4971_);
v___x_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4981_, 0, v_msg_4970_);
return v___x_4981_;
}
else
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v_c_4987_; lean_object* v___x_4988_; 
v___x_4982_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
v___x_4983_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_4984_ = l_Lean_Options_empty;
v___x_4985_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4979_);
lean_ctor_set(v___x_4985_, 1, v___x_4982_);
lean_ctor_set(v___x_4985_, 2, v___x_4983_);
lean_ctor_set(v___x_4985_, 3, v___x_4984_);
lean_inc(v_declHint_4971_);
v___x_4986_ = l_Lean_MessageData_ofConstName(v_declHint_4971_, v___x_4976_);
v_c_4987_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4987_, 0, v___x_4985_);
lean_ctor_set(v_c_4987_, 1, v___x_4986_);
v___x_4988_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4975_, v_declHint_4971_);
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
lean_dec_ref(v_env_4975_);
lean_dec(v_declHint_4971_);
v___x_4989_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_4990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
lean_ctor_set(v___x_4990_, 1, v_c_4987_);
v___x_4991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_4992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4990_);
lean_ctor_set(v___x_4992_, 1, v___x_4991_);
v___x_4993_ = l_Lean_MessageData_note(v___x_4992_);
v___x_4994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4994_, 0, v_msg_4970_);
lean_ctor_set(v___x_4994_, 1, v___x_4993_);
v___x_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4994_);
return v___x_4995_;
}
else
{
lean_object* v_val_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5031_; 
v_val_4996_ = lean_ctor_get(v___x_4988_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_4998_ = v___x_4988_;
v_isShared_4999_ = v_isSharedCheck_5031_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_val_4996_);
lean_dec(v___x_4988_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5031_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v_mod_5003_; uint8_t v___x_5004_; 
v___x_5000_ = lean_box(0);
v___x_5001_ = l_Lean_Environment_header(v_env_4975_);
lean_dec_ref(v_env_4975_);
v___x_5002_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5001_);
v_mod_5003_ = lean_array_get(v___x_5000_, v___x_5002_, v_val_4996_);
lean_dec(v_val_4996_);
lean_dec_ref(v___x_5002_);
v___x_5004_ = l_Lean_isPrivateName(v_declHint_4971_);
lean_dec(v_declHint_4971_);
if (v___x_5004_ == 0)
{
lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5016_; 
v___x_5005_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_5006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5005_);
lean_ctor_set(v___x_5006_, 1, v_c_4987_);
v___x_5007_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_5008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5008_, 0, v___x_5006_);
lean_ctor_set(v___x_5008_, 1, v___x_5007_);
v___x_5009_ = l_Lean_MessageData_ofName(v_mod_5003_);
v___x_5010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5008_);
lean_ctor_set(v___x_5010_, 1, v___x_5009_);
v___x_5011_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_5012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5010_);
lean_ctor_set(v___x_5012_, 1, v___x_5011_);
v___x_5013_ = l_Lean_MessageData_note(v___x_5012_);
v___x_5014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5014_, 0, v_msg_4970_);
lean_ctor_set(v___x_5014_, 1, v___x_5013_);
if (v_isShared_4999_ == 0)
{
lean_ctor_set_tag(v___x_4998_, 0);
lean_ctor_set(v___x_4998_, 0, v___x_5014_);
v___x_5016_ = v___x_4998_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v___x_5014_);
v___x_5016_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
return v___x_5016_;
}
}
else
{
lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5029_; 
v___x_5018_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_5019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
lean_ctor_set(v___x_5019_, 1, v_c_4987_);
v___x_5020_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
v___x_5021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5021_, 0, v___x_5019_);
lean_ctor_set(v___x_5021_, 1, v___x_5020_);
v___x_5022_ = l_Lean_MessageData_ofName(v_mod_5003_);
v___x_5023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5023_, 0, v___x_5021_);
lean_ctor_set(v___x_5023_, 1, v___x_5022_);
v___x_5024_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
v___x_5025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5025_, 0, v___x_5023_);
lean_ctor_set(v___x_5025_, 1, v___x_5024_);
v___x_5026_ = l_Lean_MessageData_note(v___x_5025_);
v___x_5027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5027_, 0, v_msg_4970_);
lean_ctor_set(v___x_5027_, 1, v___x_5026_);
if (v_isShared_4999_ == 0)
{
lean_ctor_set_tag(v___x_4998_, 0);
lean_ctor_set(v___x_4998_, 0, v___x_5027_);
v___x_5029_ = v___x_4998_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v___x_5027_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5032_; 
lean_dec_ref(v_env_4975_);
lean_dec(v_declHint_4971_);
v___x_5032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5032_, 0, v_msg_4970_);
return v___x_5032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_5033_, lean_object* v_declHint_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5033_, v_declHint_5034_, v___y_5035_);
lean_dec(v___y_5035_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_5038_, lean_object* v_declHint_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
lean_object* v___x_5045_; lean_object* v_a_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5055_; 
v___x_5045_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5038_, v_declHint_5039_, v___y_5043_);
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
v_isSharedCheck_5055_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5048_ = v___x_5045_;
v_isShared_5049_ = v_isSharedCheck_5055_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_a_5046_);
lean_dec(v___x_5045_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5055_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5053_; 
v___x_5050_ = l_Lean_unknownIdentifierMessageTag;
v___x_5051_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5050_);
lean_ctor_set(v___x_5051_, 1, v_a_5046_);
if (v_isShared_5049_ == 0)
{
lean_ctor_set(v___x_5048_, 0, v___x_5051_);
v___x_5053_ = v___x_5048_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v___x_5051_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
return v___x_5053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_5056_, lean_object* v_declHint_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_){
_start:
{
lean_object* v_res_5063_; 
v_res_5063_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5056_, v_declHint_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
return v_res_5063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_5064_, lean_object* v_msg_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_){
_start:
{
lean_object* v_fileName_5071_; lean_object* v_fileMap_5072_; lean_object* v_options_5073_; lean_object* v_currRecDepth_5074_; lean_object* v_maxRecDepth_5075_; lean_object* v_ref_5076_; lean_object* v_currNamespace_5077_; lean_object* v_openDecls_5078_; lean_object* v_initHeartbeats_5079_; lean_object* v_maxHeartbeats_5080_; lean_object* v_quotContext_5081_; lean_object* v_currMacroScope_5082_; uint8_t v_diag_5083_; lean_object* v_cancelTk_x3f_5084_; uint8_t v_suppressElabErrors_5085_; lean_object* v_inheritedTraceOptions_5086_; lean_object* v_ref_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v_fileName_5071_ = lean_ctor_get(v___y_5068_, 0);
v_fileMap_5072_ = lean_ctor_get(v___y_5068_, 1);
v_options_5073_ = lean_ctor_get(v___y_5068_, 2);
v_currRecDepth_5074_ = lean_ctor_get(v___y_5068_, 3);
v_maxRecDepth_5075_ = lean_ctor_get(v___y_5068_, 4);
v_ref_5076_ = lean_ctor_get(v___y_5068_, 5);
v_currNamespace_5077_ = lean_ctor_get(v___y_5068_, 6);
v_openDecls_5078_ = lean_ctor_get(v___y_5068_, 7);
v_initHeartbeats_5079_ = lean_ctor_get(v___y_5068_, 8);
v_maxHeartbeats_5080_ = lean_ctor_get(v___y_5068_, 9);
v_quotContext_5081_ = lean_ctor_get(v___y_5068_, 10);
v_currMacroScope_5082_ = lean_ctor_get(v___y_5068_, 11);
v_diag_5083_ = lean_ctor_get_uint8(v___y_5068_, sizeof(void*)*14);
v_cancelTk_x3f_5084_ = lean_ctor_get(v___y_5068_, 12);
v_suppressElabErrors_5085_ = lean_ctor_get_uint8(v___y_5068_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5086_ = lean_ctor_get(v___y_5068_, 13);
v_ref_5087_ = l_Lean_replaceRef(v_ref_5064_, v_ref_5076_);
lean_inc_ref(v_inheritedTraceOptions_5086_);
lean_inc(v_cancelTk_x3f_5084_);
lean_inc(v_currMacroScope_5082_);
lean_inc(v_quotContext_5081_);
lean_inc(v_maxHeartbeats_5080_);
lean_inc(v_initHeartbeats_5079_);
lean_inc(v_openDecls_5078_);
lean_inc(v_currNamespace_5077_);
lean_inc(v_maxRecDepth_5075_);
lean_inc(v_currRecDepth_5074_);
lean_inc_ref(v_options_5073_);
lean_inc_ref(v_fileMap_5072_);
lean_inc_ref(v_fileName_5071_);
v___x_5088_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5088_, 0, v_fileName_5071_);
lean_ctor_set(v___x_5088_, 1, v_fileMap_5072_);
lean_ctor_set(v___x_5088_, 2, v_options_5073_);
lean_ctor_set(v___x_5088_, 3, v_currRecDepth_5074_);
lean_ctor_set(v___x_5088_, 4, v_maxRecDepth_5075_);
lean_ctor_set(v___x_5088_, 5, v_ref_5087_);
lean_ctor_set(v___x_5088_, 6, v_currNamespace_5077_);
lean_ctor_set(v___x_5088_, 7, v_openDecls_5078_);
lean_ctor_set(v___x_5088_, 8, v_initHeartbeats_5079_);
lean_ctor_set(v___x_5088_, 9, v_maxHeartbeats_5080_);
lean_ctor_set(v___x_5088_, 10, v_quotContext_5081_);
lean_ctor_set(v___x_5088_, 11, v_currMacroScope_5082_);
lean_ctor_set(v___x_5088_, 12, v_cancelTk_x3f_5084_);
lean_ctor_set(v___x_5088_, 13, v_inheritedTraceOptions_5086_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*14, v_diag_5083_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*14 + 1, v_suppressElabErrors_5085_);
v___x_5089_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v_msg_5065_, v___y_5066_, v___y_5067_, v___x_5088_, v___y_5069_);
lean_dec_ref(v___x_5088_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_5090_, lean_object* v_msg_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_){
_start:
{
lean_object* v_res_5097_; 
v_res_5097_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5090_, v_msg_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec(v_ref_5090_);
return v_res_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_5098_, lean_object* v_msg_5099_, lean_object* v_declHint_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_){
_start:
{
lean_object* v___x_5106_; lean_object* v_a_5107_; lean_object* v___x_5108_; 
v___x_5106_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_5099_, v_declHint_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
lean_inc(v_a_5107_);
lean_dec_ref(v___x_5106_);
v___x_5108_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5098_, v_a_5107_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_5109_, lean_object* v_msg_5110_, lean_object* v_declHint_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5109_, v_msg_5110_, v_declHint_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_);
lean_dec(v___y_5115_);
lean_dec_ref(v___y_5114_);
lean_dec(v___y_5113_);
lean_dec_ref(v___y_5112_);
lean_dec(v_ref_5109_);
return v_res_5117_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5119_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_5120_ = l_Lean_stringToMessageData(v___x_5119_);
return v___x_5120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_5121_, lean_object* v_constName_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_){
_start:
{
lean_object* v___x_5128_; uint8_t v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; 
v___x_5128_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_5129_ = 0;
lean_inc(v_constName_5122_);
v___x_5130_ = l_Lean_MessageData_ofConstName(v_constName_5122_, v___x_5129_);
v___x_5131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5131_, 0, v___x_5128_);
lean_ctor_set(v___x_5131_, 1, v___x_5130_);
v___x_5132_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5133_, 0, v___x_5131_);
lean_ctor_set(v___x_5133_, 1, v___x_5132_);
v___x_5134_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5121_, v___x_5133_, v_constName_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
return v___x_5134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_5135_, lean_object* v_constName_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_){
_start:
{
lean_object* v_res_5142_; 
v_res_5142_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5135_, v_constName_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5139_);
lean_dec(v___y_5138_);
lean_dec_ref(v___y_5137_);
lean_dec(v_ref_5135_);
return v_res_5142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(lean_object* v_constName_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_){
_start:
{
lean_object* v_ref_5149_; lean_object* v___x_5150_; 
v_ref_5149_ = lean_ctor_get(v___y_5146_, 5);
v___x_5150_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5149_, v_constName_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_);
return v___x_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_);
lean_dec(v___y_5155_);
lean_dec_ref(v___y_5154_);
lean_dec(v___y_5153_);
lean_dec_ref(v___y_5152_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(lean_object* v_constName_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_){
_start:
{
lean_object* v___x_5164_; lean_object* v_env_5165_; uint8_t v___x_5166_; lean_object* v___x_5167_; 
v___x_5164_ = lean_st_ref_get(v___y_5162_);
v_env_5165_ = lean_ctor_get(v___x_5164_, 0);
lean_inc_ref(v_env_5165_);
lean_dec(v___x_5164_);
v___x_5166_ = 0;
lean_inc(v_constName_5158_);
v___x_5167_ = l_Lean_Environment_find_x3f(v_env_5165_, v_constName_5158_, v___x_5166_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v___x_5168_; 
v___x_5168_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_);
return v___x_5168_;
}
else
{
lean_object* v_val_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5176_; 
lean_dec(v_constName_5158_);
v_val_5169_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5171_ = v___x_5167_;
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_val_5169_);
lean_dec(v___x_5167_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5174_; 
if (v_isShared_5172_ == 0)
{
lean_ctor_set_tag(v___x_5171_, 0);
v___x_5174_ = v___x_5171_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_val_5169_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0___boxed(lean_object* v_constName_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_){
_start:
{
lean_object* v_res_5183_; 
v_res_5183_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_constName_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
return v_res_5183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(lean_object* v_x_5186_, lean_object* v_x_5187_, lean_object* v_x_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_){
_start:
{
if (lean_obj_tag(v_x_5186_) == 5)
{
lean_object* v_fn_5194_; lean_object* v_arg_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; 
v_fn_5194_ = lean_ctor_get(v_x_5186_, 0);
lean_inc_ref(v_fn_5194_);
v_arg_5195_ = lean_ctor_get(v_x_5186_, 1);
lean_inc_ref(v_arg_5195_);
lean_dec_ref(v_x_5186_);
v___x_5196_ = lean_array_set(v_x_5187_, v_x_5188_, v_arg_5195_);
v___x_5197_ = lean_unsigned_to_nat(1u);
v___x_5198_ = lean_nat_sub(v_x_5188_, v___x_5197_);
lean_dec(v_x_5188_);
v_x_5186_ = v_fn_5194_;
v_x_5187_ = v___x_5196_;
v_x_5188_ = v___x_5198_;
goto _start;
}
else
{
lean_dec(v_x_5188_);
if (lean_obj_tag(v_x_5186_) == 4)
{
lean_object* v_declName_5200_; lean_object* v___x_5201_; 
v_declName_5200_ = lean_ctor_get(v_x_5186_, 0);
lean_inc(v_declName_5200_);
lean_dec_ref(v_x_5186_);
v___x_5201_ = l_Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0(v_declName_5200_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5233_; 
v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5204_ = v___x_5201_;
v_isShared_5205_ = v_isSharedCheck_5233_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5201_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5233_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v_lower_5207_; lean_object* v_upper_5208_; 
if (lean_obj_tag(v_a_5202_) == 5)
{
lean_object* v_val_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5230_; 
v_val_5216_ = lean_ctor_get(v_a_5202_, 0);
v_isSharedCheck_5230_ = !lean_is_exclusive(v_a_5202_);
if (v_isSharedCheck_5230_ == 0)
{
v___x_5218_ = v_a_5202_;
v_isShared_5219_ = v_isSharedCheck_5230_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_val_5216_);
lean_dec(v_a_5202_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5230_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v_numParams_5220_; lean_object* v_numIndices_5221_; lean_object* v___x_5222_; uint8_t v___x_5223_; 
v_numParams_5220_ = lean_ctor_get(v_val_5216_, 1);
lean_inc(v_numParams_5220_);
v_numIndices_5221_ = lean_ctor_get(v_val_5216_, 2);
lean_inc(v_numIndices_5221_);
lean_dec_ref(v_val_5216_);
v___x_5222_ = lean_unsigned_to_nat(0u);
v___x_5223_ = lean_nat_dec_eq(v_numIndices_5221_, v___x_5222_);
lean_dec(v_numIndices_5221_);
if (v___x_5223_ == 0)
{
lean_object* v___x_5224_; uint8_t v___x_5225_; 
lean_del_object(v___x_5218_);
v___x_5224_ = lean_array_get_size(v_x_5187_);
v___x_5225_ = lean_nat_dec_le(v_numParams_5220_, v___x_5222_);
if (v___x_5225_ == 0)
{
v_lower_5207_ = v_numParams_5220_;
v_upper_5208_ = v___x_5224_;
goto v___jp_5206_;
}
else
{
lean_dec(v_numParams_5220_);
v_lower_5207_ = v___x_5222_;
v_upper_5208_ = v___x_5224_;
goto v___jp_5206_;
}
}
else
{
lean_object* v___x_5226_; lean_object* v___x_5228_; 
lean_dec(v_numParams_5220_);
lean_del_object(v___x_5204_);
lean_dec_ref(v_x_5187_);
v___x_5226_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___closed__0));
if (v_isShared_5219_ == 0)
{
lean_ctor_set_tag(v___x_5218_, 0);
lean_ctor_set(v___x_5218_, 0, v___x_5226_);
v___x_5228_ = v___x_5218_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v___x_5226_);
v___x_5228_ = v_reuseFailAlloc_5229_;
goto v_reusejp_5227_;
}
v_reusejp_5227_:
{
return v___x_5228_;
}
}
}
}
else
{
lean_object* v___x_5231_; lean_object* v___x_5232_; 
lean_del_object(v___x_5204_);
lean_dec(v_a_5202_);
lean_dec_ref(v_x_5187_);
v___x_5231_ = lean_box(0);
v___x_5232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5231_);
return v___x_5232_;
}
v___jp_5206_:
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5214_; 
v___x_5209_ = l_Array_toSubarray___redArg(v_x_5187_, v_lower_5207_, v_upper_5208_);
v___x_5210_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v___x_5211_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5209_, v___x_5210_);
v___x_5212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5212_, 0, v___x_5211_);
if (v_isShared_5205_ == 0)
{
lean_ctor_set(v___x_5204_, 0, v___x_5212_);
v___x_5214_ = v___x_5204_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v___x_5212_);
v___x_5214_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
return v___x_5214_;
}
}
}
}
else
{
lean_object* v_a_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5241_; 
lean_dec_ref(v_x_5187_);
v_a_5234_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5241_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5236_ = v___x_5201_;
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_a_5234_);
lean_dec(v___x_5201_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5239_; 
if (v_isShared_5237_ == 0)
{
v___x_5239_ = v___x_5236_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5240_; 
v_reuseFailAlloc_5240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5240_, 0, v_a_5234_);
v___x_5239_ = v_reuseFailAlloc_5240_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
return v___x_5239_;
}
}
}
}
else
{
lean_object* v___x_5242_; lean_object* v___x_5243_; 
lean_dec_ref(v_x_5187_);
lean_dec_ref(v_x_5186_);
v___x_5242_ = lean_box(0);
v___x_5243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5243_, 0, v___x_5242_);
return v___x_5243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2___boxed(lean_object* v_x_5244_, lean_object* v_x_5245_, lean_object* v_x_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_x_5244_, v_x_5245_, v_x_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f(lean_object* v_ctorApp_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_){
_start:
{
lean_object* v___x_5259_; 
lean_inc(v_a_5257_);
lean_inc_ref(v_a_5256_);
lean_inc(v_a_5255_);
lean_inc_ref(v_a_5254_);
v___x_5259_ = lean_infer_type(v_ctorApp_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_);
if (lean_obj_tag(v___x_5259_) == 0)
{
lean_object* v_a_5260_; lean_object* v___x_5261_; 
v_a_5260_ = lean_ctor_get(v___x_5259_, 0);
lean_inc(v_a_5260_);
lean_dec_ref(v___x_5259_);
v___x_5261_ = l_Lean_Meta_whnfD(v_a_5260_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_);
if (lean_obj_tag(v___x_5261_) == 0)
{
lean_object* v_a_5262_; lean_object* v_dummy_5263_; lean_object* v_nargs_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; 
v_a_5262_ = lean_ctor_get(v___x_5261_, 0);
lean_inc(v_a_5262_);
lean_dec_ref(v___x_5261_);
v_dummy_5263_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_elimOptParam_spec__0_spec__0___lam__1___closed__0);
v_nargs_5264_ = l_Lean_Expr_getAppNumArgs(v_a_5262_);
lean_inc(v_nargs_5264_);
v___x_5265_ = lean_mk_array(v_nargs_5264_, v_dummy_5263_);
v___x_5266_ = lean_unsigned_to_nat(1u);
v___x_5267_ = lean_nat_sub(v_nargs_5264_, v___x_5266_);
lean_dec(v_nargs_5264_);
v___x_5268_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_getCtorAppIndices_x3f_spec__2(v_a_5262_, v___x_5265_, v___x_5267_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_);
return v___x_5268_;
}
else
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5276_; 
v_a_5269_ = lean_ctor_get(v___x_5261_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5261_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5271_ = v___x_5261_;
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___x_5261_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5274_; 
if (v_isShared_5272_ == 0)
{
v___x_5274_ = v___x_5271_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5269_);
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
lean_object* v_a_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5284_; 
v_a_5277_ = lean_ctor_get(v___x_5259_, 0);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5259_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5279_ = v___x_5259_;
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_a_5277_);
lean_dec(v___x_5259_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___x_5282_; 
if (v_isShared_5280_ == 0)
{
v___x_5282_ = v___x_5279_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_a_5277_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorAppIndices_x3f___boxed(lean_object* v_ctorApp_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_){
_start:
{
lean_object* v_res_5291_; 
v_res_5291_ = l_Lean_Meta_getCtorAppIndices_x3f(v_ctorApp_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
lean_dec(v_a_5289_);
lean_dec_ref(v_a_5288_);
lean_dec(v_a_5287_);
lean_dec_ref(v_a_5286_);
return v_res_5291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1(lean_object* v_inst_5292_, lean_object* v_R_5293_, lean_object* v_a_5294_, lean_object* v_b_5295_){
_start:
{
lean_object* v___x_5296_; 
v___x_5296_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v_a_5294_, v_b_5295_);
return v___x_5296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(lean_object* v_00_u03b1_5297_, lean_object* v_constName_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
lean_object* v___x_5304_; 
v___x_5304_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___redArg(v_constName_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
return v___x_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5305_, lean_object* v_constName_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_){
_start:
{
lean_object* v_res_5312_; 
v_res_5312_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0(v_00_u03b1_5305_, v_constName_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_);
lean_dec(v___y_5310_);
lean_dec_ref(v___y_5309_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
return v_res_5312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_5313_, lean_object* v_ref_5314_, lean_object* v_constName_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_){
_start:
{
lean_object* v___x_5321_; 
v___x_5321_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___redArg(v_ref_5314_, v_constName_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_);
return v___x_5321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_5322_, lean_object* v_ref_5323_, lean_object* v_constName_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_){
_start:
{
lean_object* v_res_5330_; 
v_res_5330_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1(v_00_u03b1_5322_, v_ref_5323_, v_constName_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
lean_dec(v_ref_5323_);
return v_res_5330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_5331_, lean_object* v_ref_5332_, lean_object* v_msg_5333_, lean_object* v_declHint_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_){
_start:
{
lean_object* v___x_5340_; 
v___x_5340_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_5332_, v_msg_5333_, v_declHint_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_);
return v___x_5340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_5341_, lean_object* v_ref_5342_, lean_object* v_msg_5343_, lean_object* v_declHint_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_5341_, v_ref_5342_, v_msg_5343_, v_declHint_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec(v_ref_5342_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_5351_, lean_object* v_declHint_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_){
_start:
{
lean_object* v___x_5358_; 
v___x_5358_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_5351_, v_declHint_5352_, v___y_5356_);
return v___x_5358_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_5359_, lean_object* v_declHint_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_5359_, v_declHint_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
lean_dec(v___y_5364_);
lean_dec_ref(v___y_5363_);
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_5367_, lean_object* v_ref_5368_, lean_object* v_msg_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_){
_start:
{
lean_object* v___x_5375_; 
v___x_5375_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_5368_, v_msg_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_);
return v___x_5375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_5376_, lean_object* v_ref_5377_, lean_object* v_msg_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
lean_object* v_res_5384_; 
v_res_5384_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getCtorAppIndices_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_5376_, v_ref_5377_, v_msg_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
lean_dec(v___y_5382_);
lean_dec_ref(v___y_5381_);
lean_dec(v___y_5380_);
lean_dec_ref(v___y_5379_);
lean_dec(v_ref_5377_);
return v_res_5384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed(lean_object* v_i_5385_, lean_object* v_body_5386_, lean_object* v_args2_5387_, lean_object* v_ctorVal_5388_, lean_object* v_args1_5389_, lean_object* v_k_5390_, lean_object* v_arg2_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_){
_start:
{
lean_object* v_res_5397_; 
v_res_5397_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(v_i_5385_, v_body_5386_, v_args2_5387_, v_ctorVal_5388_, v_args1_5389_, v_k_5390_, v_arg2_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_);
lean_dec(v___y_5395_);
lean_dec_ref(v___y_5394_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
lean_dec_ref(v_body_5386_);
lean_dec(v_i_5385_);
return v_res_5397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(lean_object* v_ctorVal_5398_, lean_object* v_args1_5399_, lean_object* v_k_5400_, lean_object* v_i_5401_, lean_object* v_type_5402_, lean_object* v_args2_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_){
_start:
{
lean_object* v___x_5409_; uint8_t v___x_5410_; 
v___x_5409_ = lean_array_get_size(v_args1_5399_);
v___x_5410_ = lean_nat_dec_lt(v_i_5401_, v___x_5409_);
if (v___x_5410_ == 0)
{
lean_object* v___x_5411_; 
lean_dec_ref(v_type_5402_);
lean_dec(v_i_5401_);
lean_dec_ref(v_args1_5399_);
lean_dec_ref(v_ctorVal_5398_);
lean_inc(v_a_5407_);
lean_inc_ref(v_a_5406_);
lean_inc(v_a_5405_);
lean_inc_ref(v_a_5404_);
v___x_5411_ = lean_apply_6(v_k_5400_, v_args2_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, lean_box(0));
return v___x_5411_;
}
else
{
lean_object* v___x_5412_; 
lean_inc(v_a_5407_);
lean_inc_ref(v_a_5406_);
lean_inc(v_a_5405_);
lean_inc_ref(v_a_5404_);
v___x_5412_ = lean_whnf(v_type_5402_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_);
if (lean_obj_tag(v___x_5412_) == 0)
{
lean_object* v_a_5413_; 
v_a_5413_ = lean_ctor_get(v___x_5412_, 0);
lean_inc(v_a_5413_);
lean_dec_ref(v___x_5412_);
if (lean_obj_tag(v_a_5413_) == 7)
{
lean_object* v_binderName_5414_; lean_object* v_binderType_5415_; lean_object* v_body_5416_; lean_object* v___f_5417_; uint8_t v___x_5418_; uint8_t v___x_5419_; lean_object* v___x_5420_; 
v_binderName_5414_ = lean_ctor_get(v_a_5413_, 0);
lean_inc(v_binderName_5414_);
v_binderType_5415_ = lean_ctor_get(v_a_5413_, 1);
lean_inc_ref(v_binderType_5415_);
v_body_5416_ = lean_ctor_get(v_a_5413_, 2);
lean_inc_ref(v_body_5416_);
lean_dec_ref(v_a_5413_);
v___f_5417_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5417_, 0, v_i_5401_);
lean_closure_set(v___f_5417_, 1, v_body_5416_);
lean_closure_set(v___f_5417_, 2, v_args2_5403_);
lean_closure_set(v___f_5417_, 3, v_ctorVal_5398_);
lean_closure_set(v___f_5417_, 4, v_args1_5399_);
lean_closure_set(v___f_5417_, 5, v_k_5400_);
v___x_5418_ = 1;
v___x_5419_ = 0;
v___x_5420_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__0___redArg(v_binderName_5414_, v___x_5418_, v_binderType_5415_, v___f_5417_, v___x_5419_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_);
return v___x_5420_;
}
else
{
lean_object* v_toConstantVal_5421_; lean_object* v_name_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; 
lean_dec(v_a_5413_);
lean_dec_ref(v_args2_5403_);
lean_dec(v_i_5401_);
lean_dec_ref(v_k_5400_);
lean_dec_ref(v_args1_5399_);
v_toConstantVal_5421_ = lean_ctor_get(v_ctorVal_5398_, 0);
lean_inc_ref(v_toConstantVal_5421_);
lean_dec_ref(v_ctorVal_5398_);
v_name_5422_ = lean_ctor_get(v_toConstantVal_5421_, 0);
lean_inc(v_name_5422_);
lean_dec_ref(v_toConstantVal_5421_);
v___x_5423_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__1);
v___x_5424_ = l_Lean_MessageData_ofName(v_name_5422_);
v___x_5425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5425_, 0, v___x_5423_);
lean_ctor_set(v___x_5425_, 1, v___x_5424_);
v___x_5426_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5427_, 0, v___x_5425_);
lean_ctor_set(v___x_5427_, 1, v___x_5426_);
v___x_5428_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5427_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_);
return v___x_5428_;
}
}
else
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
lean_dec_ref(v_args2_5403_);
lean_dec(v_i_5401_);
lean_dec_ref(v_k_5400_);
lean_dec_ref(v_args1_5399_);
lean_dec_ref(v_ctorVal_5398_);
v_a_5429_ = lean_ctor_get(v___x_5412_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5412_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5412_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5412_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___lam__0(lean_object* v_i_5437_, lean_object* v_body_5438_, lean_object* v_args2_5439_, lean_object* v_ctorVal_5440_, lean_object* v_args1_5441_, lean_object* v_k_5442_, lean_object* v_arg2_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_){
_start:
{
lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; 
v___x_5449_ = lean_unsigned_to_nat(1u);
v___x_5450_ = lean_nat_add(v_i_5437_, v___x_5449_);
v___x_5451_ = lean_expr_instantiate1(v_body_5438_, v_arg2_5443_);
v___x_5452_ = lean_array_push(v_args2_5439_, v_arg2_5443_);
v___x_5453_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5440_, v_args1_5441_, v_k_5442_, v___x_5450_, v___x_5451_, v___x_5452_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
return v___x_5453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed(lean_object* v_ctorVal_5454_, lean_object* v_args1_5455_, lean_object* v_k_5456_, lean_object* v_i_5457_, lean_object* v_type_5458_, lean_object* v_args2_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_){
_start:
{
lean_object* v_res_5465_; 
v_res_5465_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2(v_ctorVal_5454_, v_args1_5455_, v_k_5456_, v_i_5457_, v_type_5458_, v_args2_5459_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_);
lean_dec(v_a_5463_);
lean_dec_ref(v_a_5462_);
lean_dec(v_a_5461_);
lean_dec_ref(v_a_5460_);
return v_res_5465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(lean_object* v_name_5466_, lean_object* v_us_5467_, lean_object* v_args1_5468_, lean_object* v___x_5469_, lean_object* v_numParams_5470_, lean_object* v___x_5471_, lean_object* v_args2_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_){
_start:
{
lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; 
lean_inc(v_us_5467_);
v___x_5478_ = l_Lean_mkConst(v_name_5466_, v_us_5467_);
lean_inc_ref(v___x_5478_);
v___x_5479_ = l_Lean_mkAppN(v___x_5478_, v_args1_5468_);
v___x_5480_ = l_Lean_mkAppN(v___x_5478_, v_args2_5472_);
lean_inc_ref(v___x_5480_);
lean_inc_ref(v___x_5479_);
v___x_5481_ = l_Lean_Meta_mkEqHEq(v___x_5479_, v___x_5480_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
if (lean_obj_tag(v___x_5481_) == 0)
{
lean_object* v_a_5482_; lean_object* v___x_5483_; uint8_t v___x_5484_; lean_object* v___x_5485_; 
v_a_5482_ = lean_ctor_get(v___x_5481_, 0);
lean_inc(v_a_5482_);
lean_dec_ref(v___x_5481_);
lean_inc_ref(v_args2_5472_);
v___x_5483_ = l_Array_toSubarray___redArg(v_args2_5472_, v___x_5469_, v_numParams_5470_);
v___x_5484_ = 1;
lean_inc_ref(v_args2_5472_);
v___x_5485_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v_args1_5468_, v_args2_5472_, v___x_5484_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v_a_5486_; lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5606_; 
v_a_5486_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5488_ = v___x_5485_;
v_isShared_5489_ = v_isSharedCheck_5606_;
goto v_resetjp_5487_;
}
else
{
lean_inc(v_a_5486_);
lean_dec(v___x_5485_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5606_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
lean_object* v___x_5490_; 
v___x_5490_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkAnd_x3f(v_a_5486_);
if (lean_obj_tag(v___x_5490_) == 1)
{
lean_object* v_val_5491_; lean_object* v___x_5492_; 
lean_del_object(v___x_5488_);
v_val_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_val_5491_);
lean_dec_ref(v___x_5490_);
v___x_5492_ = l_Lean_mkArrow(v_a_5482_, v_val_5491_, v___y_5475_, v___y_5476_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_a_5493_; lean_object* v___x_5494_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
lean_inc(v_a_5493_);
lean_dec_ref(v___x_5492_);
v___x_5494_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5479_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v_a_5495_; lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5585_; 
v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5585_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5585_ == 0)
{
v___x_5497_ = v___x_5494_;
v_isShared_5498_ = v_isSharedCheck_5585_;
goto v_resetjp_5496_;
}
else
{
lean_inc(v_a_5495_);
lean_dec(v___x_5494_);
v___x_5497_ = lean_box(0);
v_isShared_5498_ = v_isSharedCheck_5585_;
goto v_resetjp_5496_;
}
v_resetjp_5496_:
{
if (lean_obj_tag(v_a_5495_) == 1)
{
lean_object* v_val_5499_; lean_object* v___x_5500_; 
lean_del_object(v___x_5497_);
v_val_5499_ = lean_ctor_get(v_a_5495_, 0);
lean_inc(v_val_5499_);
lean_dec_ref(v_a_5495_);
v___x_5500_ = l_Lean_Meta_getCtorAppIndices_x3f(v___x_5480_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
if (lean_obj_tag(v___x_5500_) == 0)
{
lean_object* v_a_5501_; lean_object* v___x_5503_; uint8_t v_isShared_5504_; uint8_t v_isSharedCheck_5572_; 
v_a_5501_ = lean_ctor_get(v___x_5500_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5500_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5503_ = v___x_5500_;
v_isShared_5504_ = v_isSharedCheck_5572_;
goto v_resetjp_5502_;
}
else
{
lean_inc(v_a_5501_);
lean_dec(v___x_5500_);
v___x_5503_ = lean_box(0);
v_isShared_5504_ = v_isSharedCheck_5572_;
goto v_resetjp_5502_;
}
v_resetjp_5502_:
{
if (lean_obj_tag(v_a_5501_) == 1)
{
lean_object* v_val_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5567_; 
lean_del_object(v___x_5503_);
v_val_5505_ = lean_ctor_get(v_a_5501_, 0);
v_isSharedCheck_5567_ = !lean_is_exclusive(v_a_5501_);
if (v_isSharedCheck_5567_ == 0)
{
v___x_5507_ = v_a_5501_;
v_isShared_5508_ = v_isSharedCheck_5567_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_val_5505_);
lean_dec(v_a_5501_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5567_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; uint8_t v___x_5513_; lean_object* v___x_5514_; 
v___x_5509_ = l_Subarray_copy___redArg(v___x_5471_);
v___x_5510_ = l_Array_append___redArg(v___x_5509_, v_val_5499_);
v___x_5511_ = l_Subarray_copy___redArg(v___x_5483_);
v___x_5512_ = l_Array_append___redArg(v___x_5511_, v_val_5505_);
lean_dec(v_val_5505_);
v___x_5513_ = 0;
v___x_5514_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs(v___x_5510_, v___x_5512_, v___x_5513_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
lean_dec_ref(v___x_5510_);
if (lean_obj_tag(v___x_5514_) == 0)
{
lean_object* v_a_5515_; lean_object* v___x_5516_; 
v_a_5515_ = lean_ctor_get(v___x_5514_, 0);
lean_inc(v_a_5515_);
lean_dec_ref(v___x_5514_);
v___x_5516_ = l_Lean_mkArrowN(v_a_5515_, v_a_5493_, v___y_5475_, v___y_5476_);
lean_dec(v_a_5515_);
if (lean_obj_tag(v___x_5516_) == 0)
{
lean_object* v_a_5517_; uint8_t v___x_5518_; lean_object* v___x_5519_; 
v_a_5517_ = lean_ctor_get(v___x_5516_, 0);
lean_inc(v_a_5517_);
lean_dec_ref(v___x_5516_);
v___x_5518_ = 1;
v___x_5519_ = l_Lean_Meta_mkForallFVars(v_args2_5472_, v_a_5517_, v___x_5513_, v___x_5484_, v___x_5484_, v___x_5518_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
lean_dec_ref(v_args2_5472_);
if (lean_obj_tag(v___x_5519_) == 0)
{
lean_object* v_a_5520_; lean_object* v___x_5521_; 
v_a_5520_ = lean_ctor_get(v___x_5519_, 0);
lean_inc(v_a_5520_);
lean_dec_ref(v___x_5519_);
v___x_5521_ = l_Lean_Meta_mkForallFVars(v_args1_5468_, v_a_5520_, v___x_5513_, v___x_5484_, v___x_5484_, v___x_5518_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
if (lean_obj_tag(v___x_5521_) == 0)
{
lean_object* v_a_5522_; lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5534_; 
v_a_5522_ = lean_ctor_get(v___x_5521_, 0);
v_isSharedCheck_5534_ = !lean_is_exclusive(v___x_5521_);
if (v_isSharedCheck_5534_ == 0)
{
v___x_5524_ = v___x_5521_;
v_isShared_5525_ = v_isSharedCheck_5534_;
goto v_resetjp_5523_;
}
else
{
lean_inc(v_a_5522_);
lean_dec(v___x_5521_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5534_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5529_; 
v___x_5526_ = lean_array_get_size(v_val_5499_);
lean_dec(v_val_5499_);
v___x_5527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5527_, 0, v_a_5522_);
lean_ctor_set(v___x_5527_, 1, v_us_5467_);
lean_ctor_set(v___x_5527_, 2, v___x_5526_);
if (v_isShared_5508_ == 0)
{
lean_ctor_set(v___x_5507_, 0, v___x_5527_);
v___x_5529_ = v___x_5507_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v___x_5527_);
v___x_5529_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
lean_object* v___x_5531_; 
if (v_isShared_5525_ == 0)
{
lean_ctor_set(v___x_5524_, 0, v___x_5529_);
v___x_5531_ = v___x_5524_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v___x_5529_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
return v___x_5531_;
}
}
}
}
else
{
lean_object* v_a_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5542_; 
lean_del_object(v___x_5507_);
lean_dec(v_val_5499_);
lean_dec(v_us_5467_);
v_a_5535_ = lean_ctor_get(v___x_5521_, 0);
v_isSharedCheck_5542_ = !lean_is_exclusive(v___x_5521_);
if (v_isSharedCheck_5542_ == 0)
{
v___x_5537_ = v___x_5521_;
v_isShared_5538_ = v_isSharedCheck_5542_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_a_5535_);
lean_dec(v___x_5521_);
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
lean_del_object(v___x_5507_);
lean_dec(v_val_5499_);
lean_dec(v_us_5467_);
v_a_5543_ = lean_ctor_get(v___x_5519_, 0);
v_isSharedCheck_5550_ = !lean_is_exclusive(v___x_5519_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5545_ = v___x_5519_;
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
else
{
lean_inc(v_a_5543_);
lean_dec(v___x_5519_);
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
else
{
lean_object* v_a_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5558_; 
lean_del_object(v___x_5507_);
lean_dec(v_val_5499_);
lean_dec_ref(v_args2_5472_);
lean_dec(v_us_5467_);
v_a_5551_ = lean_ctor_get(v___x_5516_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5516_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5553_ = v___x_5516_;
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_a_5551_);
lean_dec(v___x_5516_);
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
lean_del_object(v___x_5507_);
lean_dec(v_val_5499_);
lean_dec(v_a_5493_);
lean_dec_ref(v_args2_5472_);
lean_dec(v_us_5467_);
v_a_5559_ = lean_ctor_get(v___x_5514_, 0);
v_isSharedCheck_5566_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5566_ == 0)
{
v___x_5561_ = v___x_5514_;
v_isShared_5562_ = v_isSharedCheck_5566_;
goto v_resetjp_5560_;
}
else
{
lean_inc(v_a_5559_);
lean_dec(v___x_5514_);
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
else
{
lean_object* v___x_5568_; lean_object* v___x_5570_; 
lean_dec(v_a_5501_);
lean_dec(v_val_5499_);
lean_dec(v_a_5493_);
lean_dec_ref(v___x_5483_);
lean_dec_ref(v_args2_5472_);
lean_dec_ref(v___x_5471_);
lean_dec(v_us_5467_);
v___x_5568_ = lean_box(0);
if (v_isShared_5504_ == 0)
{
lean_ctor_set(v___x_5503_, 0, v___x_5568_);
v___x_5570_ = v___x_5503_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5568_);
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
lean_object* v_a_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5580_; 
lean_dec(v_val_5499_);
lean_dec(v_a_5493_);
lean_dec_ref(v___x_5483_);
lean_dec_ref(v_args2_5472_);
lean_dec_ref(v___x_5471_);
lean_dec(v_us_5467_);
v_a_5573_ = lean_ctor_get(v___x_5500_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v___x_5500_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5575_ = v___x_5500_;
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_a_5573_);
lean_dec(v___x_5500_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___x_5578_; 
if (v_isShared_5576_ == 0)
{
v___x_5578_ = v___x_5575_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_a_5573_);
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
lean_object* v___x_5581_; lean_object* v___x_5583_; 
lean_dec(v_a_5495_);
lean_dec(v_a_5493_);
lean_dec_ref(v___x_5483_);
lean_dec_ref(v___x_5480_);
lean_dec_ref(v_args2_5472_);
lean_dec_ref(v___x_5471_);
lean_dec(v_us_5467_);
v___x_5581_ = lean_box(0);
if (v_isShared_5498_ == 0)
{
lean_ctor_set(v___x_5497_, 0, v___x_5581_);
v___x_5583_ = v___x_5497_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v___x_5581_);
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
lean_dec(v_a_5493_);
lean_dec_ref(v___x_5483_);
lean_dec_ref(v___x_5480_);
lean_dec_ref(v_args2_5472_);
lean_dec_ref(v___x_5471_);
lean_dec(v_us_5467_);
v_a_5586_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5593_ == 0)
{
v___x_5588_ = v___x_5494_;
v_isShared_5589_ = v_isSharedCheck_5593_;
goto v_resetjp_5587_;
}
else
{
lean_inc(v_a_5586_);
lean_dec(v___x_5494_);
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
else
{
lean_object* v_a_5594_; lean_object* v___x_5596_; uint8_t v_isShared_5597_; uint8_t v_isSharedCheck_5601_; 
lean_dec_ref(v___x_5483_);
lean_dec_ref(v___x_5480_);
lean_dec_ref(v___x_5479_);
lean_dec_ref(v_args2_5472_);
lean_dec_ref(v___x_5471_);
lean_dec(v_us_5467_);
v_a_5594_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5601_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5601_ == 0)
{
v___x_5596_ = v___x_5492_;
v_isShared_5597_ = v_isSharedCheck_5601_;
goto v_resetjp_5595_;
}
else
{
lean_inc(v_a_5594_);
lean_dec(v___x_5492_);
v___x_5596_ = lean_box(0);
v_isShared_5597_ = v_isSharedCheck_5601_;
goto v_resetjp_5595_;
}
v_resetjp_5595_:
{
lean_object* v___x_5599_; 
if (v_isShared_5597_ == 0)
{
v___x_5599_ = v___x_5596_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5600_; 
v_reuseFailAlloc_5600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5600_, 0, v_a_5594_);
v___x_5599_ = v_reuseFailAlloc_5600_;
goto v_reusejp_5598_;
}
v_reusejp_5598_:
{
return v___x_5599_;
}
}
}
}
else
{
lean_object* v___x_5602_; lean_object* v___x_5604_; 
lean_dec(v___x_5490_);
lean_dec_ref(v___x_5483_);
lean_dec(v_a_5482_);
lean_dec_ref(v___x_5480_);
lean_dec_ref(v___x_5479_);
lean_dec_ref(v_args2_5472_);
lean_dec_ref(v___x_5471_);
lean_dec(v_us_5467_);
v___x_5602_ = lean_box(0);
if (v_isShared_5489_ == 0)
{
lean_ctor_set(v___x_5488_, 0, v___x_5602_);
v___x_5604_ = v___x_5488_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5602_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
}
}
}
}
else
{
lean_object* v_a_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5614_; 
lean_dec_ref(v___x_5483_);
lean_dec(v_a_5482_);
lean_dec_ref(v___x_5480_);
lean_dec_ref(v___x_5479_);
lean_dec_ref(v_args2_5472_);
lean_dec_ref(v___x_5471_);
lean_dec(v_us_5467_);
v_a_5607_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5614_ == 0)
{
v___x_5609_ = v___x_5485_;
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_a_5607_);
lean_dec(v___x_5485_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5612_; 
if (v_isShared_5610_ == 0)
{
v___x_5612_ = v___x_5609_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_a_5607_);
v___x_5612_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
return v___x_5612_;
}
}
}
}
else
{
lean_object* v_a_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5622_; 
lean_dec_ref(v___x_5480_);
lean_dec_ref(v___x_5479_);
lean_dec_ref(v_args2_5472_);
lean_dec_ref(v___x_5471_);
lean_dec(v_numParams_5470_);
lean_dec(v___x_5469_);
lean_dec(v_us_5467_);
v_a_5615_ = lean_ctor_get(v___x_5481_, 0);
v_isSharedCheck_5622_ = !lean_is_exclusive(v___x_5481_);
if (v_isSharedCheck_5622_ == 0)
{
v___x_5617_ = v___x_5481_;
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_a_5615_);
lean_dec(v___x_5481_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5620_; 
if (v_isShared_5618_ == 0)
{
v___x_5620_ = v___x_5617_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5615_);
v___x_5620_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
return v___x_5620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed(lean_object* v_name_5623_, lean_object* v_us_5624_, lean_object* v_args1_5625_, lean_object* v___x_5626_, lean_object* v_numParams_5627_, lean_object* v___x_5628_, lean_object* v_args2_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_){
_start:
{
lean_object* v_res_5635_; 
v_res_5635_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0(v_name_5623_, v_us_5624_, v_args1_5625_, v___x_5626_, v_numParams_5627_, v___x_5628_, v_args2_5629_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec_ref(v_args1_5625_);
return v_res_5635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(lean_object* v_numParams_5636_, lean_object* v_name_5637_, lean_object* v_us_5638_, lean_object* v_ctorVal_5639_, lean_object* v_a_5640_, lean_object* v_args1_5641_, lean_object* v_x_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_){
_start:
{
lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___f_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; 
v___x_5648_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5636_);
lean_inc_ref(v_args1_5641_);
v___x_5649_ = l_Array_toSubarray___redArg(v_args1_5641_, v___x_5648_, v_numParams_5636_);
lean_inc_ref(v_args1_5641_);
v___f_5650_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__0___boxed), 12, 6);
lean_closure_set(v___f_5650_, 0, v_name_5637_);
lean_closure_set(v___f_5650_, 1, v_us_5638_);
lean_closure_set(v___f_5650_, 2, v_args1_5641_);
lean_closure_set(v___f_5650_, 3, v___x_5648_);
lean_closure_set(v___f_5650_, 4, v_numParams_5636_);
lean_closure_set(v___f_5650_, 5, v___x_5649_);
v___x_5651_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
lean_inc_ref(v_args1_5641_);
v___x_5652_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f_mkArgs2___boxed), 11, 6);
lean_closure_set(v___x_5652_, 0, v_ctorVal_5639_);
lean_closure_set(v___x_5652_, 1, v_args1_5641_);
lean_closure_set(v___x_5652_, 2, v___f_5650_);
lean_closure_set(v___x_5652_, 3, v___x_5648_);
lean_closure_set(v___x_5652_, 4, v_a_5640_);
lean_closure_set(v___x_5652_, 5, v___x_5651_);
v___x_5653_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__1___redArg(v_args1_5641_, v___x_5652_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_);
return v___x_5653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed(lean_object* v_numParams_5654_, lean_object* v_name_5655_, lean_object* v_us_5656_, lean_object* v_ctorVal_5657_, lean_object* v_a_5658_, lean_object* v_args1_5659_, lean_object* v_x_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_){
_start:
{
lean_object* v_res_5666_; 
v_res_5666_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1(v_numParams_5654_, v_name_5655_, v_us_5656_, v_ctorVal_5657_, v_a_5658_, v_args1_5659_, v_x_5660_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
lean_dec(v___y_5664_);
lean_dec_ref(v___y_5663_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
lean_dec_ref(v_x_5660_);
return v_res_5666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(lean_object* v_ctorVal_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_){
_start:
{
lean_object* v_toConstantVal_5673_; lean_object* v_numParams_5674_; lean_object* v_name_5675_; lean_object* v_levelParams_5676_; lean_object* v_type_5677_; lean_object* v___x_5678_; 
v_toConstantVal_5673_ = lean_ctor_get(v_ctorVal_5667_, 0);
v_numParams_5674_ = lean_ctor_get(v_ctorVal_5667_, 3);
lean_inc(v_numParams_5674_);
v_name_5675_ = lean_ctor_get(v_toConstantVal_5673_, 0);
lean_inc(v_name_5675_);
v_levelParams_5676_ = lean_ctor_get(v_toConstantVal_5673_, 1);
v_type_5677_ = lean_ctor_get(v_toConstantVal_5673_, 2);
lean_inc_ref(v_type_5677_);
v___x_5678_ = l_Lean_Meta_elimOptParam(v_type_5677_, v_a_5670_, v_a_5671_);
if (lean_obj_tag(v___x_5678_) == 0)
{
lean_object* v_a_5679_; lean_object* v___x_5680_; lean_object* v_us_5681_; lean_object* v___f_5682_; uint8_t v___x_5683_; lean_object* v___x_5684_; 
v_a_5679_ = lean_ctor_get(v___x_5678_, 0);
lean_inc(v_a_5679_);
lean_dec_ref(v___x_5678_);
v___x_5680_ = lean_box(0);
lean_inc(v_levelParams_5676_);
v_us_5681_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__0(v_levelParams_5676_, v___x_5680_);
lean_inc(v_a_5679_);
v___f_5682_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___lam__1___boxed), 12, 5);
lean_closure_set(v___f_5682_, 0, v_numParams_5674_);
lean_closure_set(v___f_5682_, 1, v_name_5675_);
lean_closure_set(v___f_5682_, 2, v_us_5681_);
lean_closure_set(v___f_5682_, 3, v_ctorVal_5667_);
lean_closure_set(v___f_5682_, 4, v_a_5679_);
v___x_5683_ = 0;
v___x_5684_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_spec__2___redArg(v_a_5679_, v___f_5682_, v___x_5683_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_);
return v___x_5684_;
}
else
{
lean_object* v_a_5685_; lean_object* v___x_5687_; uint8_t v_isShared_5688_; uint8_t v_isSharedCheck_5692_; 
lean_dec(v_name_5675_);
lean_dec(v_numParams_5674_);
lean_dec_ref(v_ctorVal_5667_);
v_a_5685_ = lean_ctor_get(v___x_5678_, 0);
v_isSharedCheck_5692_ = !lean_is_exclusive(v___x_5678_);
if (v_isSharedCheck_5692_ == 0)
{
v___x_5687_ = v___x_5678_;
v_isShared_5688_ = v_isSharedCheck_5692_;
goto v_resetjp_5686_;
}
else
{
lean_inc(v_a_5685_);
lean_dec(v___x_5678_);
v___x_5687_ = lean_box(0);
v_isShared_5688_ = v_isSharedCheck_5692_;
goto v_resetjp_5686_;
}
v_resetjp_5686_:
{
lean_object* v___x_5690_; 
if (v_isShared_5688_ == 0)
{
v___x_5690_ = v___x_5687_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5691_; 
v_reuseFailAlloc_5691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5691_, 0, v_a_5685_);
v___x_5690_ = v_reuseFailAlloc_5691_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
return v___x_5690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f___boxed(lean_object* v_ctorVal_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_){
_start:
{
lean_object* v_res_5699_; 
v_res_5699_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_5693_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_);
lean_dec(v_a_5697_);
lean_dec_ref(v_a_5696_);
lean_dec(v_a_5695_);
lean_dec_ref(v_a_5694_);
return v_res_5699_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1(void){
_start:
{
lean_object* v___x_5701_; lean_object* v___x_5702_; 
v___x_5701_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__0));
v___x_5702_ = l_Lean_stringToMessageData(v___x_5701_);
return v___x_5702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(lean_object* v_ctorVal_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_){
_start:
{
lean_object* v_toConstantVal_5709_; lean_object* v_name_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; 
v_toConstantVal_5709_ = lean_ctor_get(v_ctorVal_5703_, 0);
lean_inc_ref(v_toConstantVal_5709_);
lean_dec_ref(v_ctorVal_5703_);
v_name_5710_ = lean_ctor_get(v_toConstantVal_5709_, 0);
lean_inc(v_name_5710_);
lean_dec_ref(v_toConstantVal_5709_);
v___x_5711_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___closed__1);
v___x_5712_ = l_Lean_MessageData_ofName(v_name_5710_);
v___x_5713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5711_);
lean_ctor_set(v___x_5713_, 1, v___x_5712_);
v___x_5714_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2___closed__3);
v___x_5715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5713_);
lean_ctor_set(v___x_5715_, 1, v___x_5714_);
v___x_5716_ = l_Lean_throwError___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremTypeCore_x3f_mkArgs2_spec__1___redArg(v___x_5715_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_);
return v___x_5716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg___boxed(lean_object* v_ctorVal_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_){
_start:
{
lean_object* v_res_5723_; 
v_res_5723_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5717_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_);
lean_dec(v_a_5721_);
lean_dec_ref(v_a_5720_);
lean_dec(v_a_5719_);
lean_dec_ref(v_a_5718_);
return v_res_5723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(lean_object* v_00_u03b1_5724_, lean_object* v_ctorVal_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_){
_start:
{
lean_object* v___x_5731_; 
v___x_5731_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5725_, v_a_5726_, v_a_5727_, v_a_5728_, v_a_5729_);
return v___x_5731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___boxed(lean_object* v_00_u03b1_5732_, lean_object* v_ctorVal_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_){
_start:
{
lean_object* v_res_5739_; 
v_res_5739_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj(v_00_u03b1_5732_, v_ctorVal_5733_, v_a_5734_, v_a_5735_, v_a_5736_, v_a_5737_);
lean_dec(v_a_5737_);
lean_dec_ref(v_a_5736_);
lean_dec(v_a_5735_);
lean_dec_ref(v_a_5734_);
return v_res_5739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(lean_object* v_ctorVal_5745_, size_t v_sz_5746_, size_t v_i_5747_, lean_object* v_bs_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_){
_start:
{
uint8_t v___x_5754_; 
v___x_5754_ = lean_usize_dec_lt(v_i_5747_, v_sz_5746_);
if (v___x_5754_ == 0)
{
lean_object* v___x_5755_; 
lean_dec_ref(v_ctorVal_5745_);
v___x_5755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5755_, 0, v_bs_5748_);
return v___x_5755_;
}
else
{
lean_object* v_v_5756_; lean_object* v___x_5757_; 
v_v_5756_ = lean_array_uget_borrowed(v_bs_5748_, v_i_5747_);
lean_inc(v___y_5752_);
lean_inc_ref(v___y_5751_);
lean_inc(v___y_5750_);
lean_inc_ref(v___y_5749_);
lean_inc(v_v_5756_);
v___x_5757_ = lean_infer_type(v_v_5756_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_);
if (lean_obj_tag(v___x_5757_) == 0)
{
lean_object* v_a_5758_; lean_object* v___x_5759_; 
v_a_5758_ = lean_ctor_get(v___x_5757_, 0);
lean_inc(v_a_5758_);
lean_dec_ref(v___x_5757_);
v___x_5759_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_5758_, v___y_5750_);
if (lean_obj_tag(v___x_5759_) == 0)
{
lean_object* v_a_5760_; lean_object* v___x_5761_; lean_object* v_bs_x27_5762_; lean_object* v_a_5764_; lean_object* v___y_5770_; lean_object* v_lhs_5781_; lean_object* v_rhs_5782_; lean_object* v___x_5784_; uint8_t v___x_5785_; 
v_a_5760_ = lean_ctor_get(v___x_5759_, 0);
lean_inc(v_a_5760_);
lean_dec_ref(v___x_5759_);
v___x_5761_ = lean_unsigned_to_nat(0u);
v_bs_x27_5762_ = lean_array_uset(v_bs_5748_, v_i_5747_, v___x_5761_);
v___x_5784_ = l_Lean_Expr_cleanupAnnotations(v_a_5760_);
v___x_5785_ = l_Lean_Expr_isApp(v___x_5784_);
if (v___x_5785_ == 0)
{
lean_object* v___x_5786_; 
lean_dec_ref(v___x_5784_);
lean_inc_ref(v_ctorVal_5745_);
v___x_5786_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5745_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_);
v___y_5770_ = v___x_5786_;
goto v___jp_5769_;
}
else
{
lean_object* v_arg_5787_; lean_object* v___x_5788_; uint8_t v___x_5789_; 
v_arg_5787_ = lean_ctor_get(v___x_5784_, 1);
lean_inc_ref(v_arg_5787_);
v___x_5788_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5784_);
v___x_5789_ = l_Lean_Expr_isApp(v___x_5788_);
if (v___x_5789_ == 0)
{
lean_object* v___x_5790_; 
lean_dec_ref(v___x_5788_);
lean_dec_ref(v_arg_5787_);
lean_inc_ref(v_ctorVal_5745_);
v___x_5790_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5745_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_);
v___y_5770_ = v___x_5790_;
goto v___jp_5769_;
}
else
{
lean_object* v_arg_5791_; lean_object* v___x_5792_; uint8_t v___x_5793_; 
v_arg_5791_ = lean_ctor_get(v___x_5788_, 1);
lean_inc_ref(v_arg_5791_);
v___x_5792_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5788_);
v___x_5793_ = l_Lean_Expr_isApp(v___x_5792_);
if (v___x_5793_ == 0)
{
lean_object* v___x_5794_; 
lean_dec_ref(v___x_5792_);
lean_dec_ref(v_arg_5791_);
lean_dec_ref(v_arg_5787_);
lean_inc_ref(v_ctorVal_5745_);
v___x_5794_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5745_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_);
v___y_5770_ = v___x_5794_;
goto v___jp_5769_;
}
else
{
lean_object* v_arg_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; uint8_t v___x_5798_; 
v_arg_5795_ = lean_ctor_get(v___x_5792_, 1);
lean_inc_ref(v_arg_5795_);
v___x_5796_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5792_);
v___x_5797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__0));
v___x_5798_ = l_Lean_Expr_isConstOf(v___x_5796_, v___x_5797_);
if (v___x_5798_ == 0)
{
uint8_t v___x_5799_; 
lean_dec_ref(v_arg_5791_);
v___x_5799_ = l_Lean_Expr_isApp(v___x_5796_);
if (v___x_5799_ == 0)
{
lean_object* v___x_5800_; 
lean_dec_ref(v___x_5796_);
lean_dec_ref(v_arg_5795_);
lean_dec_ref(v_arg_5787_);
lean_inc_ref(v_ctorVal_5745_);
v___x_5800_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5745_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_);
v___y_5770_ = v___x_5800_;
goto v___jp_5769_;
}
else
{
lean_object* v___x_5801_; lean_object* v___x_5802_; uint8_t v___x_5803_; 
v___x_5801_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5796_);
v___x_5802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___closed__2));
v___x_5803_ = l_Lean_Expr_isConstOf(v___x_5801_, v___x_5802_);
lean_dec_ref(v___x_5801_);
if (v___x_5803_ == 0)
{
lean_object* v___x_5804_; 
lean_dec_ref(v_arg_5795_);
lean_dec_ref(v_arg_5787_);
lean_inc_ref(v_ctorVal_5745_);
v___x_5804_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5745_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_);
v___y_5770_ = v___x_5804_;
goto v___jp_5769_;
}
else
{
v_lhs_5781_ = v_arg_5795_;
v_rhs_5782_ = v_arg_5787_;
goto v___jp_5780_;
}
}
}
else
{
lean_dec_ref(v___x_5796_);
lean_dec_ref(v_arg_5795_);
v_lhs_5781_ = v_arg_5791_;
v_rhs_5782_ = v_arg_5787_;
goto v___jp_5780_;
}
}
}
}
v___jp_5763_:
{
size_t v___x_5765_; size_t v___x_5766_; lean_object* v___x_5767_; 
v___x_5765_ = ((size_t)1ULL);
v___x_5766_ = lean_usize_add(v_i_5747_, v___x_5765_);
v___x_5767_ = lean_array_uset(v_bs_x27_5762_, v_i_5747_, v_a_5764_);
v_i_5747_ = v___x_5766_;
v_bs_5748_ = v___x_5767_;
goto _start;
}
v___jp_5769_:
{
if (lean_obj_tag(v___y_5770_) == 0)
{
lean_object* v_a_5771_; 
v_a_5771_ = lean_ctor_get(v___y_5770_, 0);
lean_inc(v_a_5771_);
lean_dec_ref(v___y_5770_);
v_a_5764_ = v_a_5771_;
goto v___jp_5763_;
}
else
{
lean_object* v_a_5772_; lean_object* v___x_5774_; uint8_t v_isShared_5775_; uint8_t v_isSharedCheck_5779_; 
lean_dec_ref(v_bs_x27_5762_);
lean_dec_ref(v_ctorVal_5745_);
v_a_5772_ = lean_ctor_get(v___y_5770_, 0);
v_isSharedCheck_5779_ = !lean_is_exclusive(v___y_5770_);
if (v_isSharedCheck_5779_ == 0)
{
v___x_5774_ = v___y_5770_;
v_isShared_5775_ = v_isSharedCheck_5779_;
goto v_resetjp_5773_;
}
else
{
lean_inc(v_a_5772_);
lean_dec(v___y_5770_);
v___x_5774_ = lean_box(0);
v_isShared_5775_ = v_isSharedCheck_5779_;
goto v_resetjp_5773_;
}
v_resetjp_5773_:
{
lean_object* v___x_5777_; 
if (v_isShared_5775_ == 0)
{
v___x_5777_ = v___x_5774_;
goto v_reusejp_5776_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v_a_5772_);
v___x_5777_ = v_reuseFailAlloc_5778_;
goto v_reusejp_5776_;
}
v_reusejp_5776_:
{
return v___x_5777_;
}
}
}
}
v___jp_5780_:
{
lean_object* v___x_5783_; 
v___x_5783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5783_, 0, v_lhs_5781_);
lean_ctor_set(v___x_5783_, 1, v_rhs_5782_);
v_a_5764_ = v___x_5783_;
goto v___jp_5763_;
}
}
else
{
lean_object* v_a_5805_; lean_object* v___x_5807_; uint8_t v_isShared_5808_; uint8_t v_isSharedCheck_5812_; 
lean_dec_ref(v_bs_5748_);
lean_dec_ref(v_ctorVal_5745_);
v_a_5805_ = lean_ctor_get(v___x_5759_, 0);
v_isSharedCheck_5812_ = !lean_is_exclusive(v___x_5759_);
if (v_isSharedCheck_5812_ == 0)
{
v___x_5807_ = v___x_5759_;
v_isShared_5808_ = v_isSharedCheck_5812_;
goto v_resetjp_5806_;
}
else
{
lean_inc(v_a_5805_);
lean_dec(v___x_5759_);
v___x_5807_ = lean_box(0);
v_isShared_5808_ = v_isSharedCheck_5812_;
goto v_resetjp_5806_;
}
v_resetjp_5806_:
{
lean_object* v___x_5810_; 
if (v_isShared_5808_ == 0)
{
v___x_5810_ = v___x_5807_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5811_; 
v_reuseFailAlloc_5811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5811_, 0, v_a_5805_);
v___x_5810_ = v_reuseFailAlloc_5811_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
return v___x_5810_;
}
}
}
}
else
{
lean_object* v_a_5813_; lean_object* v___x_5815_; uint8_t v_isShared_5816_; uint8_t v_isSharedCheck_5820_; 
lean_dec_ref(v_bs_5748_);
lean_dec_ref(v_ctorVal_5745_);
v_a_5813_ = lean_ctor_get(v___x_5757_, 0);
v_isSharedCheck_5820_ = !lean_is_exclusive(v___x_5757_);
if (v_isSharedCheck_5820_ == 0)
{
v___x_5815_ = v___x_5757_;
v_isShared_5816_ = v_isSharedCheck_5820_;
goto v_resetjp_5814_;
}
else
{
lean_inc(v_a_5813_);
lean_dec(v___x_5757_);
v___x_5815_ = lean_box(0);
v_isShared_5816_ = v_isSharedCheck_5820_;
goto v_resetjp_5814_;
}
v_resetjp_5814_:
{
lean_object* v___x_5818_; 
if (v_isShared_5816_ == 0)
{
v___x_5818_ = v___x_5815_;
goto v_reusejp_5817_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_a_5813_);
v___x_5818_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5817_;
}
v_reusejp_5817_:
{
return v___x_5818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0___boxed(lean_object* v_ctorVal_5821_, lean_object* v_sz_5822_, lean_object* v_i_5823_, lean_object* v_bs_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_){
_start:
{
size_t v_sz_boxed_5830_; size_t v_i_boxed_5831_; lean_object* v_res_5832_; 
v_sz_boxed_5830_ = lean_unbox_usize(v_sz_5822_);
lean_dec(v_sz_5822_);
v_i_boxed_5831_ = lean_unbox_usize(v_i_5823_);
lean_dec(v_i_5823_);
v_res_5832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5821_, v_sz_boxed_5830_, v_i_boxed_5831_, v_bs_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_);
lean_dec(v___y_5828_);
lean_dec_ref(v___y_5827_);
lean_dec(v___y_5826_);
lean_dec_ref(v___y_5825_);
return v_res_5832_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5834_; lean_object* v___x_5835_; 
v___x_5834_ = lean_unsigned_to_nat(0u);
v___x_5835_ = l_Lean_Level_ofNat(v___x_5834_);
return v___x_5835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(lean_object* v_ctorVal_5836_, lean_object* v_us_5837_, lean_object* v_numIndices_5838_, lean_object* v_xs_5839_, lean_object* v_type_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_){
_start:
{
lean_object* v_toConstantVal_5846_; lean_object* v_induct_5847_; lean_object* v_numParams_5848_; lean_object* v___x_5849_; lean_object* v_noConfusionName_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v_noConfusion_5854_; lean_object* v_noConfusion_5855_; lean_object* v_lower_5857_; lean_object* v_upper_5858_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v_n_5969_; uint8_t v___x_5970_; 
v_toConstantVal_5846_ = lean_ctor_get(v_ctorVal_5836_, 0);
v_induct_5847_ = lean_ctor_get(v_ctorVal_5836_, 1);
v_numParams_5848_ = lean_ctor_get(v_ctorVal_5836_, 3);
v___x_5849_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__0));
lean_inc(v_induct_5847_);
v_noConfusionName_5850_ = l_Lean_Name_str___override(v_induct_5847_, v___x_5849_);
v___x_5851_ = lean_unsigned_to_nat(0u);
v___x_5852_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1, &l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___closed__1);
v___x_5853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5853_, 0, v___x_5852_);
lean_ctor_set(v___x_5853_, 1, v_us_5837_);
v_noConfusion_5854_ = l_Lean_mkConst(v_noConfusionName_5850_, v___x_5853_);
v_noConfusion_5855_ = l_Lean_Expr_app___override(v_noConfusion_5854_, v_type_5840_);
v___x_5965_ = lean_array_get_size(v_xs_5839_);
v___x_5966_ = lean_nat_sub(v___x_5965_, v_numParams_5848_);
v___x_5967_ = lean_nat_sub(v___x_5966_, v_numIndices_5838_);
lean_dec(v___x_5966_);
v___x_5968_ = lean_unsigned_to_nat(1u);
v_n_5969_ = lean_nat_sub(v___x_5967_, v___x_5968_);
lean_dec(v___x_5967_);
v___x_5970_ = lean_nat_dec_le(v_n_5969_, v___x_5851_);
if (v___x_5970_ == 0)
{
v_lower_5857_ = v_n_5969_;
v_upper_5858_ = v___x_5965_;
goto v___jp_5856_;
}
else
{
lean_dec(v_n_5969_);
v_lower_5857_ = v___x_5851_;
v_upper_5858_ = v___x_5965_;
goto v___jp_5856_;
}
v___jp_5856_:
{
lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v_eqs_5861_; size_t v_sz_5862_; size_t v___x_5863_; lean_object* v___x_5864_; 
lean_inc_ref(v_xs_5839_);
v___x_5859_ = l_Array_toSubarray___redArg(v_xs_5839_, v_lower_5857_, v_upper_5858_);
v___x_5860_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkEqs___closed__0));
v_eqs_5861_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_getCtorAppIndices_x3f_spec__1___redArg(v___x_5859_, v___x_5860_);
v_sz_5862_ = lean_array_size(v_eqs_5861_);
v___x_5863_ = ((size_t)0ULL);
lean_inc_ref(v_eqs_5861_);
lean_inc_ref(v_ctorVal_5836_);
v___x_5864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f_spec__0(v_ctorVal_5836_, v_sz_5862_, v___x_5863_, v_eqs_5861_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
if (lean_obj_tag(v___x_5864_) == 0)
{
lean_object* v_a_5865_; lean_object* v___x_5866_; lean_object* v_fst_5867_; lean_object* v_snd_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; 
v_a_5865_ = lean_ctor_get(v___x_5864_, 0);
lean_inc(v_a_5865_);
lean_dec_ref(v___x_5864_);
v___x_5866_ = l_Array_unzip___redArg(v_a_5865_);
lean_dec(v_a_5865_);
v_fst_5867_ = lean_ctor_get(v___x_5866_, 0);
lean_inc(v_fst_5867_);
v_snd_5868_ = lean_ctor_get(v___x_5866_, 1);
lean_inc(v_snd_5868_);
lean_dec_ref(v___x_5866_);
v___x_5869_ = l_Lean_mkAppN(v_noConfusion_5855_, v_fst_5867_);
lean_dec(v_fst_5867_);
v___x_5870_ = l_Lean_mkAppN(v___x_5869_, v_snd_5868_);
lean_dec(v_snd_5868_);
v___x_5871_ = l_Lean_mkAppN(v___x_5870_, v_eqs_5861_);
lean_dec_ref(v_eqs_5861_);
lean_inc(v___y_5844_);
lean_inc_ref(v___y_5843_);
lean_inc(v___y_5842_);
lean_inc_ref(v___y_5841_);
lean_inc_ref(v___x_5871_);
v___x_5872_ = lean_infer_type(v___x_5871_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
if (lean_obj_tag(v___x_5872_) == 0)
{
lean_object* v_a_5873_; lean_object* v___x_5874_; 
v_a_5873_ = lean_ctor_get(v___x_5872_, 0);
lean_inc(v_a_5873_);
lean_dec_ref(v___x_5872_);
lean_inc(v___y_5844_);
lean_inc_ref(v___y_5843_);
lean_inc(v___y_5842_);
lean_inc_ref(v___y_5841_);
v___x_5874_ = lean_whnf(v_a_5873_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
if (lean_obj_tag(v___x_5874_) == 0)
{
lean_object* v_a_5875_; 
v_a_5875_ = lean_ctor_get(v___x_5874_, 0);
lean_inc(v_a_5875_);
lean_dec_ref(v___x_5874_);
if (lean_obj_tag(v_a_5875_) == 7)
{
lean_object* v_binderType_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; 
lean_inc_ref(v_toConstantVal_5846_);
lean_dec_ref(v_ctorVal_5836_);
v_binderType_5876_ = lean_ctor_get(v_a_5875_, 1);
lean_inc_ref(v_binderType_5876_);
lean_dec_ref(v_a_5875_);
v___x_5877_ = lean_box(0);
v___x_5878_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_binderType_5876_, v___x_5877_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
if (lean_obj_tag(v___x_5878_) == 0)
{
lean_object* v_a_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; 
v_a_5879_ = lean_ctor_get(v___x_5878_, 0);
lean_inc(v_a_5879_);
lean_dec_ref(v___x_5878_);
v___x_5880_ = l_Lean_Expr_mvarId_x21(v_a_5879_);
v___x_5881_ = l_Lean_MVarId_intros(v___x_5880_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
if (lean_obj_tag(v___x_5881_) == 0)
{
lean_object* v_a_5882_; lean_object* v_snd_5883_; lean_object* v_name_5884_; lean_object* v___x_5885_; 
v_a_5882_ = lean_ctor_get(v___x_5881_, 0);
lean_inc(v_a_5882_);
lean_dec_ref(v___x_5881_);
v_snd_5883_ = lean_ctor_get(v_a_5882_, 1);
lean_inc(v_snd_5883_);
lean_dec(v_a_5882_);
v_name_5884_ = lean_ctor_get(v_toConstantVal_5846_, 0);
lean_inc(v_name_5884_);
lean_dec_ref(v_toConstantVal_5846_);
v___x_5885_ = l___private_Lean_Meta_Injective_0__Lean_Meta_splitAndAssumption(v_snd_5883_, v_name_5884_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
if (lean_obj_tag(v___x_5885_) == 0)
{
lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v_a_5888_; lean_object* v___x_5890_; uint8_t v_isShared_5891_; uint8_t v_isSharedCheck_5915_; 
lean_dec_ref(v___x_5885_);
v___x_5886_ = l_Lean_Expr_app___override(v___x_5871_, v_a_5879_);
v___x_5887_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheorem_spec__0___redArg(v___x_5886_, v___y_5842_);
v_a_5888_ = lean_ctor_get(v___x_5887_, 0);
v_isSharedCheck_5915_ = !lean_is_exclusive(v___x_5887_);
if (v_isSharedCheck_5915_ == 0)
{
v___x_5890_ = v___x_5887_;
v_isShared_5891_ = v_isSharedCheck_5915_;
goto v_resetjp_5889_;
}
else
{
lean_inc(v_a_5888_);
lean_dec(v___x_5887_);
v___x_5890_ = lean_box(0);
v_isShared_5891_ = v_isSharedCheck_5915_;
goto v_resetjp_5889_;
}
v_resetjp_5889_:
{
uint8_t v___x_5892_; uint8_t v___x_5893_; uint8_t v___x_5894_; lean_object* v___x_5895_; 
v___x_5892_ = 0;
v___x_5893_ = 1;
v___x_5894_ = 1;
v___x_5895_ = l_Lean_Meta_mkLambdaFVars(v_xs_5839_, v_a_5888_, v___x_5892_, v___x_5893_, v___x_5892_, v___x_5893_, v___x_5894_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
lean_dec_ref(v_xs_5839_);
if (lean_obj_tag(v___x_5895_) == 0)
{
lean_object* v_a_5896_; lean_object* v___x_5898_; uint8_t v_isShared_5899_; uint8_t v_isSharedCheck_5906_; 
v_a_5896_ = lean_ctor_get(v___x_5895_, 0);
v_isSharedCheck_5906_ = !lean_is_exclusive(v___x_5895_);
if (v_isSharedCheck_5906_ == 0)
{
v___x_5898_ = v___x_5895_;
v_isShared_5899_ = v_isSharedCheck_5906_;
goto v_resetjp_5897_;
}
else
{
lean_inc(v_a_5896_);
lean_dec(v___x_5895_);
v___x_5898_ = lean_box(0);
v_isShared_5899_ = v_isSharedCheck_5906_;
goto v_resetjp_5897_;
}
v_resetjp_5897_:
{
lean_object* v___x_5901_; 
if (v_isShared_5891_ == 0)
{
lean_ctor_set_tag(v___x_5890_, 1);
lean_ctor_set(v___x_5890_, 0, v_a_5896_);
v___x_5901_ = v___x_5890_;
goto v_reusejp_5900_;
}
else
{
lean_object* v_reuseFailAlloc_5905_; 
v_reuseFailAlloc_5905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5905_, 0, v_a_5896_);
v___x_5901_ = v_reuseFailAlloc_5905_;
goto v_reusejp_5900_;
}
v_reusejp_5900_:
{
lean_object* v___x_5903_; 
if (v_isShared_5899_ == 0)
{
lean_ctor_set(v___x_5898_, 0, v___x_5901_);
v___x_5903_ = v___x_5898_;
goto v_reusejp_5902_;
}
else
{
lean_object* v_reuseFailAlloc_5904_; 
v_reuseFailAlloc_5904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5904_, 0, v___x_5901_);
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
lean_object* v_a_5907_; lean_object* v___x_5909_; uint8_t v_isShared_5910_; uint8_t v_isSharedCheck_5914_; 
lean_del_object(v___x_5890_);
v_a_5907_ = lean_ctor_get(v___x_5895_, 0);
v_isSharedCheck_5914_ = !lean_is_exclusive(v___x_5895_);
if (v_isSharedCheck_5914_ == 0)
{
v___x_5909_ = v___x_5895_;
v_isShared_5910_ = v_isSharedCheck_5914_;
goto v_resetjp_5908_;
}
else
{
lean_inc(v_a_5907_);
lean_dec(v___x_5895_);
v___x_5909_ = lean_box(0);
v_isShared_5910_ = v_isSharedCheck_5914_;
goto v_resetjp_5908_;
}
v_resetjp_5908_:
{
lean_object* v___x_5912_; 
if (v_isShared_5910_ == 0)
{
v___x_5912_ = v___x_5909_;
goto v_reusejp_5911_;
}
else
{
lean_object* v_reuseFailAlloc_5913_; 
v_reuseFailAlloc_5913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5913_, 0, v_a_5907_);
v___x_5912_ = v_reuseFailAlloc_5913_;
goto v_reusejp_5911_;
}
v_reusejp_5911_:
{
return v___x_5912_;
}
}
}
}
}
else
{
lean_object* v_a_5916_; lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_5923_; 
lean_dec(v_a_5879_);
lean_dec_ref(v___x_5871_);
lean_dec_ref(v_xs_5839_);
v_a_5916_ = lean_ctor_get(v___x_5885_, 0);
v_isSharedCheck_5923_ = !lean_is_exclusive(v___x_5885_);
if (v_isSharedCheck_5923_ == 0)
{
v___x_5918_ = v___x_5885_;
v_isShared_5919_ = v_isSharedCheck_5923_;
goto v_resetjp_5917_;
}
else
{
lean_inc(v_a_5916_);
lean_dec(v___x_5885_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_5923_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
lean_object* v___x_5921_; 
if (v_isShared_5919_ == 0)
{
v___x_5921_ = v___x_5918_;
goto v_reusejp_5920_;
}
else
{
lean_object* v_reuseFailAlloc_5922_; 
v_reuseFailAlloc_5922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5922_, 0, v_a_5916_);
v___x_5921_ = v_reuseFailAlloc_5922_;
goto v_reusejp_5920_;
}
v_reusejp_5920_:
{
return v___x_5921_;
}
}
}
}
else
{
lean_object* v_a_5924_; lean_object* v___x_5926_; uint8_t v_isShared_5927_; uint8_t v_isSharedCheck_5931_; 
lean_dec(v_a_5879_);
lean_dec_ref(v___x_5871_);
lean_dec_ref(v_toConstantVal_5846_);
lean_dec_ref(v_xs_5839_);
v_a_5924_ = lean_ctor_get(v___x_5881_, 0);
v_isSharedCheck_5931_ = !lean_is_exclusive(v___x_5881_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5926_ = v___x_5881_;
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
else
{
lean_inc(v_a_5924_);
lean_dec(v___x_5881_);
v___x_5926_ = lean_box(0);
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
v_resetjp_5925_:
{
lean_object* v___x_5929_; 
if (v_isShared_5927_ == 0)
{
v___x_5929_ = v___x_5926_;
goto v_reusejp_5928_;
}
else
{
lean_object* v_reuseFailAlloc_5930_; 
v_reuseFailAlloc_5930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5930_, 0, v_a_5924_);
v___x_5929_ = v_reuseFailAlloc_5930_;
goto v_reusejp_5928_;
}
v_reusejp_5928_:
{
return v___x_5929_;
}
}
}
}
else
{
lean_object* v_a_5932_; lean_object* v___x_5934_; uint8_t v_isShared_5935_; uint8_t v_isSharedCheck_5939_; 
lean_dec_ref(v___x_5871_);
lean_dec_ref(v_toConstantVal_5846_);
lean_dec_ref(v_xs_5839_);
v_a_5932_ = lean_ctor_get(v___x_5878_, 0);
v_isSharedCheck_5939_ = !lean_is_exclusive(v___x_5878_);
if (v_isSharedCheck_5939_ == 0)
{
v___x_5934_ = v___x_5878_;
v_isShared_5935_ = v_isSharedCheck_5939_;
goto v_resetjp_5933_;
}
else
{
lean_inc(v_a_5932_);
lean_dec(v___x_5878_);
v___x_5934_ = lean_box(0);
v_isShared_5935_ = v_isSharedCheck_5939_;
goto v_resetjp_5933_;
}
v_resetjp_5933_:
{
lean_object* v___x_5937_; 
if (v_isShared_5935_ == 0)
{
v___x_5937_ = v___x_5934_;
goto v_reusejp_5936_;
}
else
{
lean_object* v_reuseFailAlloc_5938_; 
v_reuseFailAlloc_5938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5938_, 0, v_a_5932_);
v___x_5937_ = v_reuseFailAlloc_5938_;
goto v_reusejp_5936_;
}
v_reusejp_5936_:
{
return v___x_5937_;
}
}
}
}
else
{
lean_object* v___x_5940_; 
lean_dec(v_a_5875_);
lean_dec_ref(v___x_5871_);
lean_dec_ref(v_xs_5839_);
v___x_5940_ = l___private_Lean_Meta_Injective_0__Lean_Meta_failedToGenHInj___redArg(v_ctorVal_5836_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
return v___x_5940_;
}
}
else
{
lean_object* v_a_5941_; lean_object* v___x_5943_; uint8_t v_isShared_5944_; uint8_t v_isSharedCheck_5948_; 
lean_dec_ref(v___x_5871_);
lean_dec_ref(v_xs_5839_);
lean_dec_ref(v_ctorVal_5836_);
v_a_5941_ = lean_ctor_get(v___x_5874_, 0);
v_isSharedCheck_5948_ = !lean_is_exclusive(v___x_5874_);
if (v_isSharedCheck_5948_ == 0)
{
v___x_5943_ = v___x_5874_;
v_isShared_5944_ = v_isSharedCheck_5948_;
goto v_resetjp_5942_;
}
else
{
lean_inc(v_a_5941_);
lean_dec(v___x_5874_);
v___x_5943_ = lean_box(0);
v_isShared_5944_ = v_isSharedCheck_5948_;
goto v_resetjp_5942_;
}
v_resetjp_5942_:
{
lean_object* v___x_5946_; 
if (v_isShared_5944_ == 0)
{
v___x_5946_ = v___x_5943_;
goto v_reusejp_5945_;
}
else
{
lean_object* v_reuseFailAlloc_5947_; 
v_reuseFailAlloc_5947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5947_, 0, v_a_5941_);
v___x_5946_ = v_reuseFailAlloc_5947_;
goto v_reusejp_5945_;
}
v_reusejp_5945_:
{
return v___x_5946_;
}
}
}
}
else
{
lean_object* v_a_5949_; lean_object* v___x_5951_; uint8_t v_isShared_5952_; uint8_t v_isSharedCheck_5956_; 
lean_dec_ref(v___x_5871_);
lean_dec_ref(v_xs_5839_);
lean_dec_ref(v_ctorVal_5836_);
v_a_5949_ = lean_ctor_get(v___x_5872_, 0);
v_isSharedCheck_5956_ = !lean_is_exclusive(v___x_5872_);
if (v_isSharedCheck_5956_ == 0)
{
v___x_5951_ = v___x_5872_;
v_isShared_5952_ = v_isSharedCheck_5956_;
goto v_resetjp_5950_;
}
else
{
lean_inc(v_a_5949_);
lean_dec(v___x_5872_);
v___x_5951_ = lean_box(0);
v_isShared_5952_ = v_isSharedCheck_5956_;
goto v_resetjp_5950_;
}
v_resetjp_5950_:
{
lean_object* v___x_5954_; 
if (v_isShared_5952_ == 0)
{
v___x_5954_ = v___x_5951_;
goto v_reusejp_5953_;
}
else
{
lean_object* v_reuseFailAlloc_5955_; 
v_reuseFailAlloc_5955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5955_, 0, v_a_5949_);
v___x_5954_ = v_reuseFailAlloc_5955_;
goto v_reusejp_5953_;
}
v_reusejp_5953_:
{
return v___x_5954_;
}
}
}
}
else
{
lean_object* v_a_5957_; lean_object* v___x_5959_; uint8_t v_isShared_5960_; uint8_t v_isSharedCheck_5964_; 
lean_dec_ref(v_eqs_5861_);
lean_dec_ref(v_noConfusion_5855_);
lean_dec_ref(v_xs_5839_);
lean_dec_ref(v_ctorVal_5836_);
v_a_5957_ = lean_ctor_get(v___x_5864_, 0);
v_isSharedCheck_5964_ = !lean_is_exclusive(v___x_5864_);
if (v_isSharedCheck_5964_ == 0)
{
v___x_5959_ = v___x_5864_;
v_isShared_5960_ = v_isSharedCheck_5964_;
goto v_resetjp_5958_;
}
else
{
lean_inc(v_a_5957_);
lean_dec(v___x_5864_);
v___x_5959_ = lean_box(0);
v_isShared_5960_ = v_isSharedCheck_5964_;
goto v_resetjp_5958_;
}
v_resetjp_5958_:
{
lean_object* v___x_5962_; 
if (v_isShared_5960_ == 0)
{
v___x_5962_ = v___x_5959_;
goto v_reusejp_5961_;
}
else
{
lean_object* v_reuseFailAlloc_5963_; 
v_reuseFailAlloc_5963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5963_, 0, v_a_5957_);
v___x_5962_ = v_reuseFailAlloc_5963_;
goto v_reusejp_5961_;
}
v_reusejp_5961_:
{
return v___x_5962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed(lean_object* v_ctorVal_5971_, lean_object* v_us_5972_, lean_object* v_numIndices_5973_, lean_object* v_xs_5974_, lean_object* v_type_5975_, lean_object* v___y_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_){
_start:
{
lean_object* v_res_5981_; 
v_res_5981_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0(v_ctorVal_5971_, v_us_5972_, v_numIndices_5973_, v_xs_5974_, v_type_5975_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_);
lean_dec(v___y_5979_);
lean_dec_ref(v___y_5978_);
lean_dec(v___y_5977_);
lean_dec_ref(v___y_5976_);
lean_dec(v_numIndices_5973_);
return v_res_5981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(lean_object* v_ctorVal_5982_, lean_object* v_typeInfo_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_){
_start:
{
lean_object* v_thmType_5989_; lean_object* v_us_5990_; lean_object* v_numIndices_5991_; lean_object* v___f_5992_; uint8_t v___x_5993_; lean_object* v___x_5994_; 
v_thmType_5989_ = lean_ctor_get(v_typeInfo_5983_, 0);
lean_inc_ref(v_thmType_5989_);
v_us_5990_ = lean_ctor_get(v_typeInfo_5983_, 1);
lean_inc(v_us_5990_);
v_numIndices_5991_ = lean_ctor_get(v_typeInfo_5983_, 2);
lean_inc(v_numIndices_5991_);
lean_dec_ref(v_typeInfo_5983_);
v___f_5992_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5992_, 0, v_ctorVal_5982_);
lean_closure_set(v___f_5992_, 1, v_us_5990_);
lean_closure_set(v___f_5992_, 2, v_numIndices_5991_);
v___x_5993_ = 0;
v___x_5994_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Injective_0__Lean_Meta_mkInjectiveTheoremValue_spec__0___redArg(v_thmType_5989_, v___f_5992_, v___x_5993_, v___x_5993_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_);
return v___x_5994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f___boxed(lean_object* v_ctorVal_5995_, lean_object* v_typeInfo_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_, lean_object* v_a_5999_, lean_object* v_a_6000_, lean_object* v_a_6001_){
_start:
{
lean_object* v_res_6002_; 
v_res_6002_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_5995_, v_typeInfo_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_);
lean_dec(v_a_6000_);
lean_dec_ref(v_a_5999_);
lean_dec(v_a_5998_);
lean_dec_ref(v_a_5997_);
return v_res_6002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHInjectiveTheoremNameFor(lean_object* v_ctorName_6005_){
_start:
{
lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_6006_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6007_ = l_Lean_Name_str___override(v_ctorName_6005_, v___x_6006_);
return v___x_6007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(lean_object* v_thmName_6008_, lean_object* v_ctorVal_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_, lean_object* v_a_6012_, lean_object* v_a_6013_){
_start:
{
lean_object* v___x_6015_; 
lean_inc_ref(v_ctorVal_6009_);
v___x_6015_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjType_x3f(v_ctorVal_6009_, v_a_6010_, v_a_6011_, v_a_6012_, v_a_6013_);
if (lean_obj_tag(v___x_6015_) == 0)
{
lean_object* v_a_6016_; lean_object* v___x_6018_; uint8_t v_isShared_6019_; uint8_t v_isSharedCheck_6077_; 
v_a_6016_ = lean_ctor_get(v___x_6015_, 0);
v_isSharedCheck_6077_ = !lean_is_exclusive(v___x_6015_);
if (v_isSharedCheck_6077_ == 0)
{
v___x_6018_ = v___x_6015_;
v_isShared_6019_ = v_isSharedCheck_6077_;
goto v_resetjp_6017_;
}
else
{
lean_inc(v_a_6016_);
lean_dec(v___x_6015_);
v___x_6018_ = lean_box(0);
v_isShared_6019_ = v_isSharedCheck_6077_;
goto v_resetjp_6017_;
}
v_resetjp_6017_:
{
if (lean_obj_tag(v_a_6016_) == 1)
{
lean_object* v_val_6020_; lean_object* v___x_6021_; 
lean_del_object(v___x_6018_);
v_val_6020_ = lean_ctor_get(v_a_6016_, 0);
lean_inc(v_val_6020_);
lean_dec_ref(v_a_6016_);
lean_inc(v_val_6020_);
lean_inc_ref(v_ctorVal_6009_);
v___x_6021_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheoremValue_x3f(v_ctorVal_6009_, v_val_6020_, v_a_6010_, v_a_6011_, v_a_6012_, v_a_6013_);
if (lean_obj_tag(v___x_6021_) == 0)
{
lean_object* v_a_6022_; lean_object* v___x_6024_; uint8_t v_isShared_6025_; uint8_t v_isSharedCheck_6064_; 
v_a_6022_ = lean_ctor_get(v___x_6021_, 0);
v_isSharedCheck_6064_ = !lean_is_exclusive(v___x_6021_);
if (v_isSharedCheck_6064_ == 0)
{
v___x_6024_ = v___x_6021_;
v_isShared_6025_ = v_isSharedCheck_6064_;
goto v_resetjp_6023_;
}
else
{
lean_inc(v_a_6022_);
lean_dec(v___x_6021_);
v___x_6024_ = lean_box(0);
v_isShared_6025_ = v_isSharedCheck_6064_;
goto v_resetjp_6023_;
}
v_resetjp_6023_:
{
if (lean_obj_tag(v_a_6022_) == 1)
{
lean_object* v_toConstantVal_6026_; lean_object* v_val_6027_; lean_object* v___x_6029_; uint8_t v_isShared_6030_; uint8_t v_isSharedCheck_6059_; 
v_toConstantVal_6026_ = lean_ctor_get(v_ctorVal_6009_, 0);
lean_inc_ref(v_toConstantVal_6026_);
lean_dec_ref(v_ctorVal_6009_);
v_val_6027_ = lean_ctor_get(v_a_6022_, 0);
v_isSharedCheck_6059_ = !lean_is_exclusive(v_a_6022_);
if (v_isSharedCheck_6059_ == 0)
{
v___x_6029_ = v_a_6022_;
v_isShared_6030_ = v_isSharedCheck_6059_;
goto v_resetjp_6028_;
}
else
{
lean_inc(v_val_6027_);
lean_dec(v_a_6022_);
v___x_6029_ = lean_box(0);
v_isShared_6030_ = v_isSharedCheck_6059_;
goto v_resetjp_6028_;
}
v_resetjp_6028_:
{
lean_object* v_levelParams_6031_; lean_object* v___x_6033_; uint8_t v_isShared_6034_; uint8_t v_isSharedCheck_6056_; 
v_levelParams_6031_ = lean_ctor_get(v_toConstantVal_6026_, 1);
v_isSharedCheck_6056_ = !lean_is_exclusive(v_toConstantVal_6026_);
if (v_isSharedCheck_6056_ == 0)
{
lean_object* v_unused_6057_; lean_object* v_unused_6058_; 
v_unused_6057_ = lean_ctor_get(v_toConstantVal_6026_, 2);
lean_dec(v_unused_6057_);
v_unused_6058_ = lean_ctor_get(v_toConstantVal_6026_, 0);
lean_dec(v_unused_6058_);
v___x_6033_ = v_toConstantVal_6026_;
v_isShared_6034_ = v_isSharedCheck_6056_;
goto v_resetjp_6032_;
}
else
{
lean_inc(v_levelParams_6031_);
lean_dec(v_toConstantVal_6026_);
v___x_6033_ = lean_box(0);
v_isShared_6034_ = v_isSharedCheck_6056_;
goto v_resetjp_6032_;
}
v_resetjp_6032_:
{
lean_object* v_thmType_6035_; lean_object* v___x_6037_; uint8_t v_isShared_6038_; uint8_t v_isSharedCheck_6053_; 
v_thmType_6035_ = lean_ctor_get(v_val_6020_, 0);
v_isSharedCheck_6053_ = !lean_is_exclusive(v_val_6020_);
if (v_isSharedCheck_6053_ == 0)
{
lean_object* v_unused_6054_; lean_object* v_unused_6055_; 
v_unused_6054_ = lean_ctor_get(v_val_6020_, 2);
lean_dec(v_unused_6054_);
v_unused_6055_ = lean_ctor_get(v_val_6020_, 1);
lean_dec(v_unused_6055_);
v___x_6037_ = v_val_6020_;
v_isShared_6038_ = v_isSharedCheck_6053_;
goto v_resetjp_6036_;
}
else
{
lean_inc(v_thmType_6035_);
lean_dec(v_val_6020_);
v___x_6037_ = lean_box(0);
v_isShared_6038_ = v_isSharedCheck_6053_;
goto v_resetjp_6036_;
}
v_resetjp_6036_:
{
lean_object* v___x_6040_; 
lean_inc(v_thmName_6008_);
if (v_isShared_6034_ == 0)
{
lean_ctor_set(v___x_6033_, 2, v_thmType_6035_);
lean_ctor_set(v___x_6033_, 0, v_thmName_6008_);
v___x_6040_ = v___x_6033_;
goto v_reusejp_6039_;
}
else
{
lean_object* v_reuseFailAlloc_6052_; 
v_reuseFailAlloc_6052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6052_, 0, v_thmName_6008_);
lean_ctor_set(v_reuseFailAlloc_6052_, 1, v_levelParams_6031_);
lean_ctor_set(v_reuseFailAlloc_6052_, 2, v_thmType_6035_);
v___x_6040_ = v_reuseFailAlloc_6052_;
goto v_reusejp_6039_;
}
v_reusejp_6039_:
{
lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6044_; 
v___x_6041_ = lean_box(0);
v___x_6042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6042_, 0, v_thmName_6008_);
lean_ctor_set(v___x_6042_, 1, v___x_6041_);
if (v_isShared_6038_ == 0)
{
lean_ctor_set(v___x_6037_, 2, v___x_6042_);
lean_ctor_set(v___x_6037_, 1, v_val_6027_);
lean_ctor_set(v___x_6037_, 0, v___x_6040_);
v___x_6044_ = v___x_6037_;
goto v_reusejp_6043_;
}
else
{
lean_object* v_reuseFailAlloc_6051_; 
v_reuseFailAlloc_6051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6051_, 0, v___x_6040_);
lean_ctor_set(v_reuseFailAlloc_6051_, 1, v_val_6027_);
lean_ctor_set(v_reuseFailAlloc_6051_, 2, v___x_6042_);
v___x_6044_ = v_reuseFailAlloc_6051_;
goto v_reusejp_6043_;
}
v_reusejp_6043_:
{
lean_object* v___x_6046_; 
if (v_isShared_6030_ == 0)
{
lean_ctor_set(v___x_6029_, 0, v___x_6044_);
v___x_6046_ = v___x_6029_;
goto v_reusejp_6045_;
}
else
{
lean_object* v_reuseFailAlloc_6050_; 
v_reuseFailAlloc_6050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6050_, 0, v___x_6044_);
v___x_6046_ = v_reuseFailAlloc_6050_;
goto v_reusejp_6045_;
}
v_reusejp_6045_:
{
lean_object* v___x_6048_; 
if (v_isShared_6025_ == 0)
{
lean_ctor_set(v___x_6024_, 0, v___x_6046_);
v___x_6048_ = v___x_6024_;
goto v_reusejp_6047_;
}
else
{
lean_object* v_reuseFailAlloc_6049_; 
v_reuseFailAlloc_6049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6049_, 0, v___x_6046_);
v___x_6048_ = v_reuseFailAlloc_6049_;
goto v_reusejp_6047_;
}
v_reusejp_6047_:
{
return v___x_6048_;
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
lean_object* v___x_6060_; lean_object* v___x_6062_; 
lean_dec(v_a_6022_);
lean_dec(v_val_6020_);
lean_dec_ref(v_ctorVal_6009_);
lean_dec(v_thmName_6008_);
v___x_6060_ = lean_box(0);
if (v_isShared_6025_ == 0)
{
lean_ctor_set(v___x_6024_, 0, v___x_6060_);
v___x_6062_ = v___x_6024_;
goto v_reusejp_6061_;
}
else
{
lean_object* v_reuseFailAlloc_6063_; 
v_reuseFailAlloc_6063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6063_, 0, v___x_6060_);
v___x_6062_ = v_reuseFailAlloc_6063_;
goto v_reusejp_6061_;
}
v_reusejp_6061_:
{
return v___x_6062_;
}
}
}
}
else
{
lean_object* v_a_6065_; lean_object* v___x_6067_; uint8_t v_isShared_6068_; uint8_t v_isSharedCheck_6072_; 
lean_dec(v_val_6020_);
lean_dec_ref(v_ctorVal_6009_);
lean_dec(v_thmName_6008_);
v_a_6065_ = lean_ctor_get(v___x_6021_, 0);
v_isSharedCheck_6072_ = !lean_is_exclusive(v___x_6021_);
if (v_isSharedCheck_6072_ == 0)
{
v___x_6067_ = v___x_6021_;
v_isShared_6068_ = v_isSharedCheck_6072_;
goto v_resetjp_6066_;
}
else
{
lean_inc(v_a_6065_);
lean_dec(v___x_6021_);
v___x_6067_ = lean_box(0);
v_isShared_6068_ = v_isSharedCheck_6072_;
goto v_resetjp_6066_;
}
v_resetjp_6066_:
{
lean_object* v___x_6070_; 
if (v_isShared_6068_ == 0)
{
v___x_6070_ = v___x_6067_;
goto v_reusejp_6069_;
}
else
{
lean_object* v_reuseFailAlloc_6071_; 
v_reuseFailAlloc_6071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6071_, 0, v_a_6065_);
v___x_6070_ = v_reuseFailAlloc_6071_;
goto v_reusejp_6069_;
}
v_reusejp_6069_:
{
return v___x_6070_;
}
}
}
}
else
{
lean_object* v___x_6073_; lean_object* v___x_6075_; 
lean_dec(v_a_6016_);
lean_dec_ref(v_ctorVal_6009_);
lean_dec(v_thmName_6008_);
v___x_6073_ = lean_box(0);
if (v_isShared_6019_ == 0)
{
lean_ctor_set(v___x_6018_, 0, v___x_6073_);
v___x_6075_ = v___x_6018_;
goto v_reusejp_6074_;
}
else
{
lean_object* v_reuseFailAlloc_6076_; 
v_reuseFailAlloc_6076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6076_, 0, v___x_6073_);
v___x_6075_ = v_reuseFailAlloc_6076_;
goto v_reusejp_6074_;
}
v_reusejp_6074_:
{
return v___x_6075_;
}
}
}
}
else
{
lean_object* v_a_6078_; lean_object* v___x_6080_; uint8_t v_isShared_6081_; uint8_t v_isSharedCheck_6085_; 
lean_dec_ref(v_ctorVal_6009_);
lean_dec(v_thmName_6008_);
v_a_6078_ = lean_ctor_get(v___x_6015_, 0);
v_isSharedCheck_6085_ = !lean_is_exclusive(v___x_6015_);
if (v_isSharedCheck_6085_ == 0)
{
v___x_6080_ = v___x_6015_;
v_isShared_6081_ = v_isSharedCheck_6085_;
goto v_resetjp_6079_;
}
else
{
lean_inc(v_a_6078_);
lean_dec(v___x_6015_);
v___x_6080_ = lean_box(0);
v_isShared_6081_ = v_isSharedCheck_6085_;
goto v_resetjp_6079_;
}
v_resetjp_6079_:
{
lean_object* v___x_6083_; 
if (v_isShared_6081_ == 0)
{
v___x_6083_ = v___x_6080_;
goto v_reusejp_6082_;
}
else
{
lean_object* v_reuseFailAlloc_6084_; 
v_reuseFailAlloc_6084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6084_, 0, v_a_6078_);
v___x_6083_ = v_reuseFailAlloc_6084_;
goto v_reusejp_6082_;
}
v_reusejp_6082_:
{
return v___x_6083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f___boxed(lean_object* v_thmName_6086_, lean_object* v_ctorVal_6087_, lean_object* v_a_6088_, lean_object* v_a_6089_, lean_object* v_a_6090_, lean_object* v_a_6091_, lean_object* v_a_6092_){
_start:
{
lean_object* v_res_6093_; 
v_res_6093_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_thmName_6086_, v_ctorVal_6087_, v_a_6088_, v_a_6089_, v_a_6090_, v_a_6091_);
lean_dec(v_a_6091_);
lean_dec_ref(v_a_6090_);
lean_dec(v_a_6089_);
lean_dec_ref(v_a_6088_);
return v_res_6093_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(lean_object* v_env_6094_, lean_object* v_n_6095_){
_start:
{
if (lean_obj_tag(v_n_6095_) == 1)
{
lean_object* v_pre_6096_; lean_object* v_str_6097_; lean_object* v___x_6098_; uint8_t v___x_6099_; 
v_pre_6096_ = lean_ctor_get(v_n_6095_, 0);
lean_inc(v_pre_6096_);
v_str_6097_ = lean_ctor_get(v_n_6095_, 1);
lean_inc_ref(v_str_6097_);
lean_dec_ref(v_n_6095_);
v___x_6098_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6099_ = lean_string_dec_eq(v_str_6097_, v___x_6098_);
lean_dec_ref(v_str_6097_);
if (v___x_6099_ == 0)
{
lean_dec(v_pre_6096_);
lean_dec_ref(v_env_6094_);
return v___x_6099_;
}
else
{
uint8_t v___x_6100_; lean_object* v___x_6101_; 
v___x_6100_ = 0;
v___x_6101_ = l_Lean_Environment_find_x3f(v_env_6094_, v_pre_6096_, v___x_6100_);
if (lean_obj_tag(v___x_6101_) == 1)
{
lean_object* v_val_6102_; 
v_val_6102_ = lean_ctor_get(v___x_6101_, 0);
lean_inc(v_val_6102_);
lean_dec_ref(v___x_6101_);
if (lean_obj_tag(v_val_6102_) == 6)
{
lean_dec_ref(v_val_6102_);
return v___x_6099_;
}
else
{
lean_dec(v_val_6102_);
return v___x_6100_;
}
}
else
{
lean_dec(v___x_6101_);
return v___x_6100_;
}
}
}
else
{
uint8_t v___x_6103_; 
lean_dec(v_n_6095_);
lean_dec_ref(v_env_6094_);
v___x_6103_ = 0;
return v___x_6103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_env_6104_, lean_object* v_n_6105_){
_start:
{
uint8_t v_res_6106_; lean_object* v_r_6107_; 
v_res_6106_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(v_env_6104_, v_n_6105_);
v_r_6107_ = lean_box(v_res_6106_);
return v_r_6107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6110_; lean_object* v___x_6111_; 
v___f_6110_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_));
v___x_6111_ = l_Lean_registerReservedNamePredicate(v___f_6110_);
return v___x_6111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2____boxed(lean_object* v_a_6112_){
_start:
{
lean_object* v_res_6113_; 
v_res_6113_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_2395338317____hygCtx___hyg_2_();
return v_res_6113_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_thm_6114_, lean_object* v___y_6115_){
_start:
{
lean_object* v___x_6117_; lean_object* v_env_6118_; lean_object* v_toConstantVal_6119_; lean_object* v_value_6120_; lean_object* v_all_6121_; uint8_t v___y_6123_; lean_object* v_type_6131_; uint8_t v___x_6132_; 
v___x_6117_ = lean_st_ref_get(v___y_6115_);
v_env_6118_ = lean_ctor_get(v___x_6117_, 0);
lean_inc_ref(v_env_6118_);
lean_dec(v___x_6117_);
v_toConstantVal_6119_ = lean_ctor_get(v_thm_6114_, 0);
v_value_6120_ = lean_ctor_get(v_thm_6114_, 1);
v_all_6121_ = lean_ctor_get(v_thm_6114_, 2);
v_type_6131_ = lean_ctor_get(v_toConstantVal_6119_, 2);
lean_inc_ref(v_env_6118_);
v___x_6132_ = l_Lean_Environment_hasUnsafe(v_env_6118_, v_type_6131_);
if (v___x_6132_ == 0)
{
uint8_t v___x_6133_; 
v___x_6133_ = l_Lean_Environment_hasUnsafe(v_env_6118_, v_value_6120_);
v___y_6123_ = v___x_6133_;
goto v___jp_6122_;
}
else
{
lean_dec_ref(v_env_6118_);
v___y_6123_ = v___x_6132_;
goto v___jp_6122_;
}
v___jp_6122_:
{
if (v___y_6123_ == 0)
{
lean_object* v___x_6124_; lean_object* v___x_6125_; 
v___x_6124_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6124_, 0, v_thm_6114_);
v___x_6125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6124_);
return v___x_6125_;
}
else
{
lean_object* v___x_6126_; uint8_t v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; 
lean_inc(v_all_6121_);
lean_inc_ref(v_value_6120_);
lean_inc_ref(v_toConstantVal_6119_);
lean_dec_ref(v_thm_6114_);
v___x_6126_ = lean_box(0);
v___x_6127_ = 0;
v___x_6128_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6128_, 0, v_toConstantVal_6119_);
lean_ctor_set(v___x_6128_, 1, v_value_6120_);
lean_ctor_set(v___x_6128_, 2, v___x_6126_);
lean_ctor_set(v___x_6128_, 3, v_all_6121_);
lean_ctor_set_uint8(v___x_6128_, sizeof(void*)*4, v___x_6127_);
v___x_6129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6128_);
v___x_6130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6130_, 0, v___x_6129_);
return v___x_6130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_thm_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_){
_start:
{
lean_object* v_res_6137_; 
v_res_6137_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6134_, v___y_6135_);
lean_dec(v___y_6135_);
return v_res_6137_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(lean_object* v_thm_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_){
_start:
{
lean_object* v___x_6144_; 
v___x_6144_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_thm_6138_, v___y_6142_);
return v___x_6144_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_thm_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_){
_start:
{
lean_object* v_res_6151_; 
v_res_6151_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0(v_thm_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_);
lean_dec(v___y_6149_);
lean_dec_ref(v___y_6148_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
return v_res_6151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v_val_6152_, uint8_t v___x_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_){
_start:
{
lean_object* v___x_6159_; lean_object* v_a_6160_; lean_object* v___x_6161_; 
v___x_6159_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__spec__0___redArg(v_val_6152_, v___y_6157_);
v_a_6160_ = lean_ctor_get(v___x_6159_, 0);
lean_inc(v_a_6160_);
lean_dec_ref(v___x_6159_);
v___x_6161_ = l_Lean_addDecl(v_a_6160_, v___x_6153_, v___y_6156_, v___y_6157_);
return v___x_6161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_val_6162_, lean_object* v___x_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_){
_start:
{
uint8_t v___x_2122__boxed_6169_; lean_object* v_res_6170_; 
v___x_2122__boxed_6169_ = lean_unbox(v___x_6163_);
v_res_6170_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v_val_6162_, v___x_2122__boxed_6169_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_);
lean_dec(v___y_6167_);
lean_dec_ref(v___y_6166_);
lean_dec(v___y_6165_);
lean_dec_ref(v___y_6164_);
return v_res_6170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; 
v___x_6173_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6174_ = lean_unsigned_to_nat(0u);
v___x_6175_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_6175_, 0, v___x_6174_);
lean_ctor_set(v___x_6175_, 1, v___x_6174_);
lean_ctor_set(v___x_6175_, 2, v___x_6174_);
lean_ctor_set(v___x_6175_, 3, v___x_6173_);
lean_ctor_set(v___x_6175_, 4, v___x_6173_);
lean_ctor_set(v___x_6175_, 5, v___x_6173_);
lean_ctor_set(v___x_6175_, 6, v___x_6173_);
lean_ctor_set(v___x_6175_, 7, v___x_6173_);
lean_ctor_set(v___x_6175_, 8, v___x_6173_);
return v___x_6175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6176_; lean_object* v___x_6177_; 
v___x_6176_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6177_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6177_, 0, v___x_6176_);
lean_ctor_set(v___x_6177_, 1, v___x_6176_);
lean_ctor_set(v___x_6177_, 2, v___x_6176_);
lean_ctor_set(v___x_6177_, 3, v___x_6176_);
lean_ctor_set(v___x_6177_, 4, v___x_6176_);
lean_ctor_set(v___x_6177_, 5, v___x_6176_);
return v___x_6177_;
}
}
static lean_object* _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6178_; lean_object* v___x_6179_; 
v___x_6178_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__1, &l_Lean_Meta_mkInjectiveTheorems___closed__1_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__1);
v___x_6179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6178_);
lean_ctor_set(v___x_6179_, 1, v___x_6178_);
lean_ctor_set(v___x_6179_, 2, v___x_6178_);
lean_ctor_set(v___x_6179_, 3, v___x_6178_);
lean_ctor_set(v___x_6179_, 4, v___x_6178_);
return v___x_6179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(lean_object* v___x_6180_, lean_object* v_name_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_){
_start:
{
if (lean_obj_tag(v_name_6181_) == 1)
{
lean_object* v_pre_6193_; lean_object* v_str_6194_; lean_object* v___x_6195_; uint8_t v___x_6196_; 
v_pre_6193_ = lean_ctor_get(v_name_6181_, 0);
lean_inc(v_pre_6193_);
v_str_6194_ = lean_ctor_get(v_name_6181_, 1);
v___x_6195_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_hinjSuffix___closed__0));
v___x_6196_ = lean_string_dec_eq(v_str_6194_, v___x_6195_);
if (v___x_6196_ == 0)
{
lean_dec_ref(v_name_6181_);
lean_dec(v_pre_6193_);
lean_dec(v___x_6180_);
goto v___jp_6189_;
}
else
{
lean_object* v___x_6197_; lean_object* v_env_6198_; uint8_t v___x_6199_; lean_object* v___x_6200_; 
v___x_6197_ = lean_st_ref_get(v___y_6183_);
v_env_6198_ = lean_ctor_get(v___x_6197_, 0);
lean_inc_ref(v_env_6198_);
lean_dec(v___x_6197_);
v___x_6199_ = 0;
lean_inc(v_pre_6193_);
v___x_6200_ = l_Lean_Environment_find_x3f(v_env_6198_, v_pre_6193_, v___x_6199_);
if (lean_obj_tag(v___x_6200_) == 1)
{
lean_object* v_val_6201_; 
v_val_6201_ = lean_ctor_get(v___x_6200_, 0);
lean_inc(v_val_6201_);
lean_dec_ref(v___x_6200_);
if (lean_obj_tag(v_val_6201_) == 6)
{
lean_object* v_val_6202_; lean_object* v___x_6204_; uint8_t v_isShared_6205_; uint8_t v_isSharedCheck_6252_; 
v_val_6202_ = lean_ctor_get(v_val_6201_, 0);
v_isSharedCheck_6252_ = !lean_is_exclusive(v_val_6201_);
if (v_isSharedCheck_6252_ == 0)
{
v___x_6204_ = v_val_6201_;
v_isShared_6205_ = v_isSharedCheck_6252_;
goto v_resetjp_6203_;
}
else
{
lean_inc(v_val_6202_);
lean_dec(v_val_6201_);
v___x_6204_ = lean_box(0);
v_isShared_6205_ = v_isSharedCheck_6252_;
goto v_resetjp_6203_;
}
v_resetjp_6203_:
{
uint8_t v___x_6206_; uint8_t v___x_6207_; uint8_t v___x_6208_; lean_object* v___x_6209_; uint64_t v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; uint8_t v_a_6224_; lean_object* v___x_6230_; 
v___x_6206_ = 1;
v___x_6207_ = 0;
v___x_6208_ = 2;
v___x_6209_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_6209_, 0, v___x_6199_);
lean_ctor_set_uint8(v___x_6209_, 1, v___x_6199_);
lean_ctor_set_uint8(v___x_6209_, 2, v___x_6199_);
lean_ctor_set_uint8(v___x_6209_, 3, v___x_6199_);
lean_ctor_set_uint8(v___x_6209_, 4, v___x_6199_);
lean_ctor_set_uint8(v___x_6209_, 5, v___x_6196_);
lean_ctor_set_uint8(v___x_6209_, 6, v___x_6196_);
lean_ctor_set_uint8(v___x_6209_, 7, v___x_6199_);
lean_ctor_set_uint8(v___x_6209_, 8, v___x_6196_);
lean_ctor_set_uint8(v___x_6209_, 9, v___x_6206_);
lean_ctor_set_uint8(v___x_6209_, 10, v___x_6207_);
lean_ctor_set_uint8(v___x_6209_, 11, v___x_6196_);
lean_ctor_set_uint8(v___x_6209_, 12, v___x_6196_);
lean_ctor_set_uint8(v___x_6209_, 13, v___x_6196_);
lean_ctor_set_uint8(v___x_6209_, 14, v___x_6208_);
lean_ctor_set_uint8(v___x_6209_, 15, v___x_6196_);
lean_ctor_set_uint8(v___x_6209_, 16, v___x_6196_);
lean_ctor_set_uint8(v___x_6209_, 17, v___x_6196_);
lean_ctor_set_uint8(v___x_6209_, 18, v___x_6196_);
v___x_6210_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6209_);
v___x_6211_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6211_, 0, v___x_6209_);
lean_ctor_set_uint64(v___x_6211_, sizeof(void*)*1, v___x_6210_);
v___x_6212_ = lean_unsigned_to_nat(0u);
v___x_6213_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__3, &l_Lean_Meta_mkInjectiveTheorems___closed__3_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__3);
v___x_6214_ = lean_obj_once(&l_Lean_Meta_mkInjectiveTheorems___closed__4, &l_Lean_Meta_mkInjectiveTheorems___closed__4_once, _init_l_Lean_Meta_mkInjectiveTheorems___closed__4);
v___x_6215_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6216_ = lean_box(0);
lean_inc(v___x_6180_);
v___x_6217_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6217_, 0, v___x_6211_);
lean_ctor_set(v___x_6217_, 1, v___x_6180_);
lean_ctor_set(v___x_6217_, 2, v___x_6214_);
lean_ctor_set(v___x_6217_, 3, v___x_6215_);
lean_ctor_set(v___x_6217_, 4, v___x_6216_);
lean_ctor_set(v___x_6217_, 5, v___x_6212_);
lean_ctor_set(v___x_6217_, 6, v___x_6216_);
lean_ctor_set_uint8(v___x_6217_, sizeof(void*)*7, v___x_6199_);
lean_ctor_set_uint8(v___x_6217_, sizeof(void*)*7 + 1, v___x_6199_);
lean_ctor_set_uint8(v___x_6217_, sizeof(void*)*7 + 2, v___x_6199_);
lean_ctor_set_uint8(v___x_6217_, sizeof(void*)*7 + 3, v___x_6196_);
v___x_6218_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6219_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6220_ = lean_obj_once(&l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_, &l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_);
v___x_6221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6221_, 0, v___x_6218_);
lean_ctor_set(v___x_6221_, 1, v___x_6219_);
lean_ctor_set(v___x_6221_, 2, v___x_6180_);
lean_ctor_set(v___x_6221_, 3, v___x_6213_);
lean_ctor_set(v___x_6221_, 4, v___x_6220_);
v___x_6222_ = lean_st_mk_ref(v___x_6221_);
lean_inc_ref(v_name_6181_);
v___x_6230_ = l___private_Lean_Meta_Injective_0__Lean_Meta_mkHInjectiveTheorem_x3f(v_name_6181_, v_val_6202_, v___x_6217_, v___x_6222_, v___y_6182_, v___y_6183_);
if (lean_obj_tag(v___x_6230_) == 0)
{
lean_object* v_a_6231_; 
v_a_6231_ = lean_ctor_get(v___x_6230_, 0);
lean_inc(v_a_6231_);
lean_dec_ref(v___x_6230_);
if (lean_obj_tag(v_a_6231_) == 1)
{
lean_object* v_val_6232_; lean_object* v___x_6233_; lean_object* v___f_6234_; lean_object* v___x_6235_; 
v_val_6232_ = lean_ctor_get(v_a_6231_, 0);
lean_inc(v_val_6232_);
lean_dec_ref(v_a_6231_);
v___x_6233_ = lean_box(v___x_6199_);
v___f_6234_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed), 7, 2);
lean_closure_set(v___f_6234_, 0, v_val_6232_);
lean_closure_set(v___f_6234_, 1, v___x_6233_);
lean_inc_ref(v___y_6182_);
v___x_6235_ = l_Lean_Meta_realizeConst(v_pre_6193_, v_name_6181_, v___f_6234_, v___x_6217_, v___x_6222_, v___y_6182_, v___y_6183_);
lean_dec_ref(v___x_6217_);
if (lean_obj_tag(v___x_6235_) == 0)
{
lean_dec_ref(v___x_6235_);
v_a_6224_ = v___x_6196_;
goto v___jp_6223_;
}
else
{
lean_object* v_a_6236_; lean_object* v___x_6238_; uint8_t v_isShared_6239_; uint8_t v_isSharedCheck_6243_; 
lean_dec(v___x_6222_);
lean_del_object(v___x_6204_);
v_a_6236_ = lean_ctor_get(v___x_6235_, 0);
v_isSharedCheck_6243_ = !lean_is_exclusive(v___x_6235_);
if (v_isSharedCheck_6243_ == 0)
{
v___x_6238_ = v___x_6235_;
v_isShared_6239_ = v_isSharedCheck_6243_;
goto v_resetjp_6237_;
}
else
{
lean_inc(v_a_6236_);
lean_dec(v___x_6235_);
v___x_6238_ = lean_box(0);
v_isShared_6239_ = v_isSharedCheck_6243_;
goto v_resetjp_6237_;
}
v_resetjp_6237_:
{
lean_object* v___x_6241_; 
if (v_isShared_6239_ == 0)
{
v___x_6241_ = v___x_6238_;
goto v_reusejp_6240_;
}
else
{
lean_object* v_reuseFailAlloc_6242_; 
v_reuseFailAlloc_6242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6242_, 0, v_a_6236_);
v___x_6241_ = v_reuseFailAlloc_6242_;
goto v_reusejp_6240_;
}
v_reusejp_6240_:
{
return v___x_6241_;
}
}
}
}
else
{
lean_dec(v_a_6231_);
lean_dec_ref(v___x_6217_);
lean_dec_ref(v_name_6181_);
lean_dec(v_pre_6193_);
v_a_6224_ = v___x_6199_;
goto v___jp_6223_;
}
}
else
{
lean_object* v_a_6244_; lean_object* v___x_6246_; uint8_t v_isShared_6247_; uint8_t v_isSharedCheck_6251_; 
lean_dec(v___x_6222_);
lean_dec_ref(v___x_6217_);
lean_del_object(v___x_6204_);
lean_dec_ref(v_name_6181_);
lean_dec(v_pre_6193_);
v_a_6244_ = lean_ctor_get(v___x_6230_, 0);
v_isSharedCheck_6251_ = !lean_is_exclusive(v___x_6230_);
if (v_isSharedCheck_6251_ == 0)
{
v___x_6246_ = v___x_6230_;
v_isShared_6247_ = v_isSharedCheck_6251_;
goto v_resetjp_6245_;
}
else
{
lean_inc(v_a_6244_);
lean_dec(v___x_6230_);
v___x_6246_ = lean_box(0);
v_isShared_6247_ = v_isSharedCheck_6251_;
goto v_resetjp_6245_;
}
v_resetjp_6245_:
{
lean_object* v___x_6249_; 
if (v_isShared_6247_ == 0)
{
v___x_6249_ = v___x_6246_;
goto v_reusejp_6248_;
}
else
{
lean_object* v_reuseFailAlloc_6250_; 
v_reuseFailAlloc_6250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6250_, 0, v_a_6244_);
v___x_6249_ = v_reuseFailAlloc_6250_;
goto v_reusejp_6248_;
}
v_reusejp_6248_:
{
return v___x_6249_;
}
}
}
v___jp_6223_:
{
lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6228_; 
v___x_6225_ = lean_st_ref_get(v___x_6222_);
lean_dec(v___x_6222_);
lean_dec(v___x_6225_);
v___x_6226_ = lean_box(v_a_6224_);
if (v_isShared_6205_ == 0)
{
lean_ctor_set_tag(v___x_6204_, 0);
lean_ctor_set(v___x_6204_, 0, v___x_6226_);
v___x_6228_ = v___x_6204_;
goto v_reusejp_6227_;
}
else
{
lean_object* v_reuseFailAlloc_6229_; 
v_reuseFailAlloc_6229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6229_, 0, v___x_6226_);
v___x_6228_ = v_reuseFailAlloc_6229_;
goto v_reusejp_6227_;
}
v_reusejp_6227_:
{
return v___x_6228_;
}
}
}
}
else
{
lean_dec(v_val_6201_);
lean_dec_ref(v_name_6181_);
lean_dec(v_pre_6193_);
lean_dec(v___x_6180_);
goto v___jp_6185_;
}
}
else
{
lean_dec(v___x_6200_);
lean_dec_ref(v_name_6181_);
lean_dec(v_pre_6193_);
lean_dec(v___x_6180_);
goto v___jp_6185_;
}
}
}
else
{
lean_dec(v_name_6181_);
lean_dec(v___x_6180_);
goto v___jp_6189_;
}
v___jp_6185_:
{
uint8_t v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; 
v___x_6186_ = 0;
v___x_6187_ = lean_box(v___x_6186_);
v___x_6188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6187_);
return v___x_6188_;
}
v___jp_6189_:
{
uint8_t v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; 
v___x_6190_ = 0;
v___x_6191_ = lean_box(v___x_6190_);
v___x_6192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6192_, 0, v___x_6191_);
return v___x_6192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v___x_6253_, lean_object* v_name_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_){
_start:
{
lean_object* v_res_6258_; 
v_res_6258_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(v___x_6253_, v_name_6254_, v___y_6255_, v___y_6256_);
lean_dec(v___y_6256_);
lean_dec_ref(v___y_6255_);
return v_res_6258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_6262_; lean_object* v___x_6263_; 
v___f_6262_ = ((lean_object*)(l___private_Lean_Meta_Injective_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_));
v___x_6263_ = l_Lean_registerReservedNameAction(v___f_6262_);
return v___x_6263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2____boxed(lean_object* v_a_6264_){
_start:
{
lean_object* v_res_6265_; 
v_res_6265_ = l___private_Lean_Meta_Injective_0__Lean_Meta_initFn_00___x40_Lean_Meta_Injective_677622092____hygCtx___hyg_2_();
return v_res_6265_;
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
