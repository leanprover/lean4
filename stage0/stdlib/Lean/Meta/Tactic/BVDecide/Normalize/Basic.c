// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Basic
// Imports: public import Lean.Meta.Tactic.BVDecide.Attr public import Std.Tactic.BVDecide.Syntax public import Lean.Meta.Sym.ExprPtr public import Lean.Meta.Sym.SymM public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.DSimp.Result public import Lean.Meta.Tactic.Grind.Types
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
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_Result_getResultExpr(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarIdTarget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarIdTarget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_grindTarget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_grindTarget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget_default = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedTarget_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_grind_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_grind_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0;
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "assumption "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "enum domain size lemma for "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "structure lemma projection: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "and flattening from "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grind state"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__38;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__39;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__40;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__41;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Learned hypothesis: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__42 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__42_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__43;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Running pass: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object**);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Fixpoint iteration solved the goal"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Pipeline reached a fixpoint"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Rerunning pipeline"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v_contextDependent_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_12_; 
v_contextDependent_3_ = lean_ctor_get_uint8(v_x_2_, 1);
v_isSharedCheck_12_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_12_ == 0)
{
v___x_5_ = v_x_2_;
v_isShared_6_ = v_isSharedCheck_12_;
goto v_resetjp_4_;
}
else
{
lean_dec(v_x_2_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_12_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
uint8_t v___x_7_; lean_object* v___x_9_; 
v___x_7_ = 1;
if (v_isShared_6_ == 0)
{
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_11_, 1, v_contextDependent_3_);
v___x_9_ = v_reuseFailAlloc_11_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
lean_object* v___x_10_; 
lean_ctor_set_uint8(v___x_9_, 0, v___x_7_);
v___x_10_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_9_);
return v___x_10_;
}
}
}
else
{
lean_object* v_e_x27_13_; lean_object* v_proof_14_; uint8_t v_contextDependent_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v_e_x27_13_ = lean_ctor_get(v_x_2_, 0);
v_proof_14_ = lean_ctor_get(v_x_2_, 1);
v_contextDependent_15_ = lean_ctor_get_uint8(v_x_2_, sizeof(void*)*2 + 1);
v_isSharedCheck_24_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_24_ == 0)
{
v___x_17_ = v_x_2_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_proof_14_);
lean_inc(v_e_x27_13_);
lean_dec(v_x_2_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
uint8_t v___x_19_; lean_object* v___x_21_; 
v___x_19_ = 1;
if (v_isShared_18_ == 0)
{
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_e_x27_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_proof_14_);
lean_ctor_set_uint8(v_reuseFailAlloc_23_, sizeof(void*)*2 + 1, v_contextDependent_15_);
v___x_21_ = v_reuseFailAlloc_23_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_22_; 
lean_ctor_set_uint8(v___x_21_, sizeof(void*)*2, v___x_19_);
v___x_22_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_21_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg(lean_object* v_inst_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_toApplicative_27_; lean_object* v_toBind_28_; lean_object* v_toPure_29_; lean_object* v___f_30_; lean_object* v___x_31_; 
v_toApplicative_27_ = lean_ctor_get(v_inst_25_, 0);
lean_inc_ref(v_toApplicative_27_);
v_toBind_28_ = lean_ctor_get(v_inst_25_, 1);
lean_inc(v_toBind_28_);
lean_dec_ref(v_inst_25_);
v_toPure_29_ = lean_ctor_get(v_toApplicative_27_, 1);
lean_inc(v_toPure_29_);
lean_dec_ref(v_toApplicative_27_);
v___f_30_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg___lam__0), 2, 1);
lean_closure_set(v___f_30_, 0, v_toPure_29_);
v___x_31_ = lean_apply_4(v_toBind_28_, lean_box(0), lean_box(0), v_x_26_, v___f_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult(lean_object* v_m_32_, lean_object* v_inst_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_toApplicative_35_; lean_object* v_toBind_36_; lean_object* v_toPure_37_; lean_object* v___f_38_; lean_object* v___x_39_; 
v_toApplicative_35_ = lean_ctor_get(v_inst_33_, 0);
lean_inc_ref(v_toApplicative_35_);
v_toBind_36_ = lean_ctor_get(v_inst_33_, 1);
lean_inc(v_toBind_36_);
lean_dec_ref(v_inst_33_);
v_toPure_37_ = lean_ctor_get(v_toApplicative_35_, 1);
lean_inc(v_toPure_37_);
lean_dec_ref(v_toApplicative_35_);
v___f_38_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withDoneResult___redArg___lam__0), 2, 1);
lean_closure_set(v___f_38_, 0, v_toPure_37_);
v___x_39_ = lean_apply_4(v_toBind_36_, lean_box(0), lean_box(0), v_x_34_, v___f_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx(lean_object* v_x_40_){
_start:
{
if (lean_obj_tag(v_x_40_) == 0)
{
lean_object* v___x_41_; 
v___x_41_ = lean_unsigned_to_nat(0u);
return v___x_41_;
}
else
{
lean_object* v___x_42_; 
v___x_42_ = lean_unsigned_to_nat(1u);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorIdx(v_x_43_);
lean_dec_ref(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(lean_object* v_t_45_, lean_object* v_k_46_){
_start:
{
if (lean_obj_tag(v_t_45_) == 0)
{
lean_object* v_mvar_47_; lean_object* v___x_48_; 
v_mvar_47_ = lean_ctor_get(v_t_45_, 0);
lean_inc(v_mvar_47_);
lean_dec_ref_known(v_t_45_, 1);
v___x_48_ = lean_apply_1(v_k_46_, v_mvar_47_);
return v___x_48_;
}
else
{
lean_object* v_goal_49_; lean_object* v___x_50_; 
v_goal_49_ = lean_ctor_get(v_t_45_, 0);
lean_inc_ref(v_goal_49_);
lean_dec_ref_known(v_t_45_, 1);
v___x_50_ = lean_apply_1(v_k_46_, v_goal_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim(lean_object* v_motive_51_, lean_object* v_ctorIdx_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_k_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_53_, v_k_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___boxed(lean_object* v_motive_57_, lean_object* v_ctorIdx_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_k_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim(v_motive_57_, v_ctorIdx_58_, v_t_59_, v_h_60_, v_k_61_);
lean_dec(v_ctorIdx_58_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarIdTarget_elim___redArg(lean_object* v_t_63_, lean_object* v_mvarIdTarget_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_63_, v_mvarIdTarget_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarIdTarget_elim(lean_object* v_motive_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_mvarIdTarget_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_67_, v_mvarIdTarget_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_grindTarget_elim___redArg(lean_object* v_t_71_, lean_object* v_grindTarget_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_71_, v_grindTarget_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_grindTarget_elim(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_grindTarget_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_ctorElim___redArg(v_t_75_, v_grindTarget_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
lean_object* v_mvar_84_; 
v_mvar_84_ = lean_ctor_get(v_x_83_, 0);
lean_inc(v_mvar_84_);
return v_mvar_84_;
}
else
{
lean_object* v_goal_85_; lean_object* v_mvarId_86_; 
v_goal_85_ = lean_ctor_get(v_x_83_, 0);
v_mvarId_86_ = lean_ctor_get(v_goal_85_, 1);
lean_inc(v_mvarId_86_);
return v_mvarId_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId___boxed(lean_object* v_x_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_x_87_);
lean_dec_ref(v_x_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(lean_object* v_x_89_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
lean_object* v___x_90_; 
v___x_90_ = lean_unsigned_to_nat(0u);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
v___x_91_ = lean_unsigned_to_nat(1u);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___boxed(lean_object* v_x_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(v_x_92_);
lean_dec_ref(v_x_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(lean_object* v_t_94_, lean_object* v_k_95_){
_start:
{
lean_object* v_info_96_; lean_object* v_ctors_97_; lean_object* v___x_98_; 
v_info_96_ = lean_ctor_get(v_t_94_, 0);
lean_inc_ref(v_info_96_);
v_ctors_97_ = lean_ctor_get(v_t_94_, 1);
lean_inc_ref(v_ctors_97_);
lean_dec_ref(v_t_94_);
v___x_98_ = lean_apply_2(v_k_95_, v_info_96_, v_ctors_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(lean_object* v_motive_99_, lean_object* v_ctorIdx_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_k_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_101_, v_k_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(lean_object* v_motive_105_, lean_object* v_ctorIdx_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_k_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(v_motive_105_, v_ctorIdx_106_, v_t_107_, v_h_108_, v_k_109_);
lean_dec(v_ctorIdx_106_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object* v_t_111_, lean_object* v_simpleEnum_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_111_, v_simpleEnum_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(lean_object* v_motive_114_, lean_object* v_t_115_, lean_object* v_h_116_, lean_object* v_simpleEnum_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_115_, v_simpleEnum_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object* v_t_119_, lean_object* v_enumWithDefault_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_119_, v_enumWithDefault_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(lean_object* v_motive_122_, lean_object* v_t_123_, lean_object* v_h_124_, lean_object* v_enumWithDefault_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_123_, v_enumWithDefault_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo(lean_object* v_x_127_){
_start:
{
lean_object* v_info_128_; 
v_info_128_ = lean_ctor_get(v_x_127_, 0);
lean_inc_ref(v_info_128_);
return v_info_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo___boxed(lean_object* v_x_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_getEnumInfo(v_x_129_);
lean_dec_ref(v_x_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx(lean_object* v_x_131_){
_start:
{
switch(lean_obj_tag(v_x_131_))
{
case 0:
{
lean_object* v___x_132_; 
v___x_132_ = lean_unsigned_to_nat(0u);
return v___x_132_;
}
case 1:
{
lean_object* v___x_133_; 
v___x_133_ = lean_unsigned_to_nat(1u);
return v___x_133_;
}
case 2:
{
lean_object* v___x_134_; 
v___x_134_ = lean_unsigned_to_nat(2u);
return v___x_134_;
}
case 3:
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(3u);
return v___x_135_;
}
default: 
{
lean_object* v___x_136_; 
v___x_136_ = lean_unsigned_to_nat(4u);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___boxed(lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx(v_x_137_);
lean_dec(v_x_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(lean_object* v_t_139_, lean_object* v_k_140_){
_start:
{
switch(lean_obj_tag(v_t_139_))
{
case 2:
{
lean_object* v_e_141_; lean_object* v___x_142_; 
v_e_141_ = lean_ctor_get(v_t_139_, 0);
lean_inc_ref(v_e_141_);
lean_dec_ref_known(v_t_139_, 1);
v___x_142_ = lean_apply_1(v_k_140_, v_e_141_);
return v___x_142_;
}
case 4:
{
return v_k_140_;
}
default: 
{
lean_object* v_fvar_143_; lean_object* v___x_144_; 
v_fvar_143_ = lean_ctor_get(v_t_139_, 0);
lean_inc(v_fvar_143_);
lean_dec(v_t_139_);
v___x_144_ = lean_apply_1(v_k_140_, v_fvar_143_);
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(lean_object* v_motive_145_, lean_object* v_ctorIdx_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_k_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_147_, v_k_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___boxed(lean_object* v_motive_151_, lean_object* v_ctorIdx_152_, lean_object* v_t_153_, lean_object* v_h_154_, lean_object* v_k_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(v_motive_151_, v_ctorIdx_152_, v_t_153_, v_h_154_, v_k_155_);
lean_dec(v_ctorIdx_152_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim___redArg(lean_object* v_t_157_, lean_object* v_lctx_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_157_, v_lctx_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim(lean_object* v_motive_160_, lean_object* v_t_161_, lean_object* v_h_162_, lean_object* v_lctx_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_161_, v_lctx_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim___redArg(lean_object* v_t_165_, lean_object* v_enumDomain_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_165_, v_enumDomain_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim(lean_object* v_motive_168_, lean_object* v_t_169_, lean_object* v_h_170_, lean_object* v_enumDomain_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_169_, v_enumDomain_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim___redArg(lean_object* v_t_173_, lean_object* v_structureProjection_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_173_, v_structureProjection_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim(lean_object* v_motive_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_structureProjection_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_177_, v_structureProjection_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim___redArg(lean_object* v_t_181_, lean_object* v_andFlattened_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_181_, v_andFlattened_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim(lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_andFlattened_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_185_, v_andFlattened_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_grind_elim___redArg(lean_object* v_t_189_, lean_object* v_grind_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_189_, v_grind_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_grind_elim(lean_object* v_motive_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_grind_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_193_, v_grind_195_);
return v___x_196_;
}
}
static uint64_t _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0(void){
_start:
{
uint64_t v___x_201_; uint64_t v___x_202_; uint64_t v___x_203_; 
v___x_201_ = 1723ULL;
v___x_202_ = 1ULL;
v___x_203_ = lean_uint64_mix_hash(v___x_202_, v___x_201_);
return v___x_203_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(lean_object* v_x_204_){
_start:
{
switch(lean_obj_tag(v_x_204_))
{
case 0:
{
lean_object* v_fvar_205_; uint64_t v___x_206_; uint64_t v___x_207_; uint64_t v___x_208_; 
v_fvar_205_ = lean_ctor_get(v_x_204_, 0);
v___x_206_ = 0ULL;
v___x_207_ = l_Lean_instHashableFVarId_hash(v_fvar_205_);
v___x_208_ = lean_uint64_mix_hash(v___x_206_, v___x_207_);
return v___x_208_;
}
case 1:
{
lean_object* v_n_209_; uint64_t v___x_210_; 
v_n_209_ = lean_ctor_get(v_x_204_, 0);
v___x_210_ = 1ULL;
if (lean_obj_tag(v_n_209_) == 0)
{
uint64_t v___x_211_; 
v___x_211_ = lean_uint64_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0);
return v___x_211_;
}
else
{
uint64_t v_hash_212_; uint64_t v___x_213_; 
v_hash_212_ = lean_ctor_get_uint64(v_n_209_, sizeof(void*)*2);
v___x_213_ = lean_uint64_mix_hash(v___x_210_, v_hash_212_);
return v___x_213_;
}
}
case 2:
{
lean_object* v_e_214_; uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; 
v_e_214_ = lean_ctor_get(v_x_204_, 0);
v___x_215_ = 2ULL;
v___x_216_ = l_Lean_Expr_hash(v_e_214_);
v___x_217_ = lean_uint64_mix_hash(v___x_215_, v___x_216_);
return v___x_217_;
}
case 3:
{
lean_object* v_s_218_; uint64_t v___x_219_; uint64_t v___x_220_; uint64_t v___x_221_; 
v_s_218_ = lean_ctor_get(v_x_204_, 0);
v___x_219_ = 3ULL;
v___x_220_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_s_218_);
v___x_221_ = lean_uint64_mix_hash(v___x_219_, v___x_220_);
return v___x_221_;
}
default: 
{
uint64_t v___x_222_; 
v___x_222_ = 4ULL;
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed(lean_object* v_x_223_){
_start:
{
uint64_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_x_223_);
lean_dec(v_x_223_);
v_r_225_ = lean_box_uint64(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
switch(lean_obj_tag(v_x_228_))
{
case 0:
{
if (lean_obj_tag(v_x_229_) == 0)
{
lean_object* v_fvar_230_; lean_object* v_fvar_231_; uint8_t v___x_232_; 
v_fvar_230_ = lean_ctor_get(v_x_228_, 0);
v_fvar_231_ = lean_ctor_get(v_x_229_, 0);
v___x_232_ = l_Lean_instBEqFVarId_beq(v_fvar_230_, v_fvar_231_);
return v___x_232_;
}
else
{
uint8_t v___x_233_; 
v___x_233_ = 0;
return v___x_233_;
}
}
case 1:
{
if (lean_obj_tag(v_x_229_) == 1)
{
lean_object* v_n_234_; lean_object* v_n_235_; uint8_t v___x_236_; 
v_n_234_ = lean_ctor_get(v_x_228_, 0);
v_n_235_ = lean_ctor_get(v_x_229_, 0);
v___x_236_ = lean_name_eq(v_n_234_, v_n_235_);
return v___x_236_;
}
else
{
uint8_t v___x_237_; 
v___x_237_ = 0;
return v___x_237_;
}
}
case 2:
{
if (lean_obj_tag(v_x_229_) == 2)
{
lean_object* v_e_238_; lean_object* v_e_239_; uint8_t v___x_240_; 
v_e_238_ = lean_ctor_get(v_x_228_, 0);
v_e_239_ = lean_ctor_get(v_x_229_, 0);
v___x_240_ = lean_expr_eqv(v_e_238_, v_e_239_);
return v___x_240_;
}
else
{
uint8_t v___x_241_; 
v___x_241_ = 0;
return v___x_241_;
}
}
case 3:
{
if (lean_obj_tag(v_x_229_) == 3)
{
lean_object* v_s_242_; lean_object* v_s_243_; 
v_s_242_ = lean_ctor_get(v_x_228_, 0);
v_s_243_ = lean_ctor_get(v_x_229_, 0);
v_x_228_ = v_s_242_;
v_x_229_ = v_s_243_;
goto _start;
}
else
{
uint8_t v___x_245_; 
v___x_245_ = 0;
return v___x_245_;
}
}
default: 
{
if (lean_obj_tag(v_x_229_) == 4)
{
uint8_t v___x_246_; 
v___x_246_ = 1;
return v___x_246_;
}
else
{
uint8_t v___x_247_; 
v___x_247_ = 0;
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed(lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(v_x_248_, v_x_249_);
lean_dec(v_x_249_);
lean_dec(v_x_248_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(lean_object* v_s_254_){
_start:
{
if (lean_obj_tag(v_s_254_) == 3)
{
lean_object* v_s_255_; 
v_s_255_ = lean_ctor_get(v_s_254_, 0);
v_s_254_ = v_s_255_;
goto _start;
}
else
{
lean_inc(v_s_254_);
return v_s_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten___boxed(lean_object* v_s_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_257_);
lean_dec(v_s_257_);
return v_res_258_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0));
v___x_261_ = l_Lean_stringToMessageData(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2));
v___x_264_ = l_Lean_stringToMessageData(v___x_263_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4));
v___x_267_ = l_Lean_stringToMessageData(v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6));
v___x_270_ = l_Lean_stringToMessageData(v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__8));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object* v_s_274_){
_start:
{
switch(lean_obj_tag(v_s_274_))
{
case 0:
{
lean_object* v_fvar_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_fvar_275_ = lean_ctor_get(v_s_274_, 0);
lean_inc(v_fvar_275_);
lean_dec_ref_known(v_s_274_, 1);
v___x_276_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1);
v___x_277_ = l_Lean_mkFVar(v_fvar_275_);
v___x_278_ = l_Lean_MessageData_ofExpr(v___x_277_);
v___x_279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_276_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
return v___x_279_;
}
case 1:
{
lean_object* v_n_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_n_280_ = lean_ctor_get(v_s_274_, 0);
lean_inc(v_n_280_);
lean_dec_ref_known(v_s_274_, 1);
v___x_281_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3);
v___x_282_ = l_Lean_MessageData_ofName(v_n_280_);
v___x_283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
return v___x_283_;
}
case 2:
{
lean_object* v_e_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_e_284_ = lean_ctor_get(v_s_274_, 0);
lean_inc_ref(v_e_284_);
lean_dec_ref_known(v_s_274_, 1);
v___x_285_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5);
v___x_286_ = l_Lean_MessageData_ofExpr(v_e_284_);
v___x_287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
return v___x_287_;
}
case 3:
{
lean_object* v_s_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_s_288_ = lean_ctor_get(v_s_274_, 0);
lean_inc(v_s_288_);
lean_dec_ref_known(v_s_274_, 1);
v___x_289_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7);
v___x_290_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_288_);
lean_dec(v_s_288_);
v___x_291_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v___x_290_);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_289_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
return v___x_292_;
}
default: 
{
lean_object* v___x_293_; 
v___x_293_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__9);
return v___x_293_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_box(0);
v___x_300_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1));
v___x_301_ = l_Lean_Expr_const___override(v___x_300_, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_302_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default));
v___x_303_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2);
v___x_304_ = lean_box(0);
v___x_305_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
lean_ctor_set(v___x_305_, 2, v___x_303_);
lean_ctor_set(v___x_305_, 3, v___x_302_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default(void){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp(void){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
return v___x_307_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(lean_object* v_lhs_308_, lean_object* v_rhs_309_){
_start:
{
lean_object* v_type_310_; lean_object* v_type_311_; uint8_t v___x_312_; 
v_type_310_ = lean_ctor_get(v_lhs_308_, 1);
v_type_311_ = lean_ctor_get(v_rhs_309_, 1);
v___x_312_ = lean_expr_eqv(v_type_310_, v_type_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object* v_lhs_313_, lean_object* v_rhs_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(v_lhs_313_, v_rhs_314_);
lean_dec_ref(v_rhs_314_);
lean_dec_ref(v_lhs_313_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(lean_object* v_hyp_319_){
_start:
{
lean_object* v_type_320_; uint64_t v___x_321_; 
v_type_320_ = lean_ctor_get(v_hyp_319_, 1);
v___x_321_ = l_Lean_Expr_hash(v_type_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed(lean_object* v_hyp_322_){
_start:
{
uint64_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(v_hyp_322_);
lean_dec_ref(v_hyp_322_);
v_r_324_ = lean_box_uint64(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0(lean_object* v_hyp_327_){
_start:
{
lean_object* v_type_328_; lean_object* v___x_329_; 
v_type_328_ = lean_ctor_get(v_hyp_327_, 1);
lean_inc_ref(v_type_328_);
lean_dec_ref(v_hyp_327_);
v___x_329_ = l_Lean_MessageData_ofExpr(v_type_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object* v_hyp_337_, lean_object* v_result_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
if (lean_obj_tag(v_result_338_) == 0)
{
lean_object* v___x_345_; 
lean_dec_ref_known(v_result_338_, 0);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v_hyp_337_);
return v___x_345_;
}
else
{
lean_object* v_e_x27_346_; lean_object* v_proof_347_; lean_object* v_name_348_; lean_object* v_type_349_; lean_object* v_value_350_; lean_object* v_source_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_380_; 
v_e_x27_346_ = lean_ctor_get(v_result_338_, 0);
lean_inc_ref(v_e_x27_346_);
v_proof_347_ = lean_ctor_get(v_result_338_, 1);
lean_inc_ref(v_proof_347_);
lean_dec_ref_known(v_result_338_, 2);
v_name_348_ = lean_ctor_get(v_hyp_337_, 0);
v_type_349_ = lean_ctor_get(v_hyp_337_, 1);
v_value_350_ = lean_ctor_get(v_hyp_337_, 2);
v_source_351_ = lean_ctor_get(v_hyp_337_, 3);
v_isSharedCheck_380_ = !lean_is_exclusive(v_hyp_337_);
if (v_isSharedCheck_380_ == 0)
{
v___x_353_ = v_hyp_337_;
v_isShared_354_ = v_isSharedCheck_380_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_source_351_);
lean_inc(v_value_350_);
lean_inc(v_type_349_);
lean_inc(v_name_348_);
lean_dec(v_hyp_337_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_380_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; 
lean_inc_ref(v_type_349_);
v___x_355_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_349_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_371_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_371_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_371_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_371_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_360_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2));
v___x_361_ = lean_box(0);
v___x_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_362_, 0, v_a_356_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = l_Lean_mkConst(v___x_360_, v___x_362_);
lean_inc_ref(v_e_x27_346_);
v___x_364_ = l_Lean_mkApp4(v___x_363_, v_type_349_, v_e_x27_346_, v_proof_347_, v_value_350_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 2, v___x_364_);
lean_ctor_set(v___x_353_, 1, v_e_x27_346_);
v___x_366_ = v___x_353_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_name_348_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_e_x27_346_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_source_351_);
v___x_366_ = v_reuseFailAlloc_370_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_366_);
v___x_368_ = v___x_358_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_del_object(v___x_353_);
lean_dec(v_source_351_);
lean_dec_ref(v_value_350_);
lean_dec_ref(v_type_349_);
lean_dec(v_name_348_);
lean_dec_ref(v_proof_347_);
lean_dec_ref(v_e_x27_346_);
v_a_372_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_355_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_355_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___boxed(lean_object* v_hyp_381_, lean_object* v_result_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_381_, v_result_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(lean_object* v_hyp_390_, lean_object* v_result_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_390_, v_result_391_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___boxed(lean_object* v_hyp_400_, lean_object* v_result_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(v_hyp_400_, v_result_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(lean_object* v_hyp_410_, lean_object* v_result_411_){
_start:
{
lean_object* v_name_413_; lean_object* v_type_414_; lean_object* v_value_415_; lean_object* v_source_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_425_; 
v_name_413_ = lean_ctor_get(v_hyp_410_, 0);
v_type_414_ = lean_ctor_get(v_hyp_410_, 1);
v_value_415_ = lean_ctor_get(v_hyp_410_, 2);
v_source_416_ = lean_ctor_get(v_hyp_410_, 3);
v_isSharedCheck_425_ = !lean_is_exclusive(v_hyp_410_);
if (v_isSharedCheck_425_ == 0)
{
v___x_418_ = v_hyp_410_;
v_isShared_419_ = v_isSharedCheck_425_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_source_416_);
lean_inc(v_value_415_);
lean_inc(v_type_414_);
lean_inc(v_name_413_);
lean_dec(v_hyp_410_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_425_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = l_Lean_Meta_Sym_DSimp_Result_getResultExpr(v_type_414_, v_result_411_);
lean_dec_ref(v_type_414_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 1, v___x_420_);
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_name_413_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_value_415_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_source_416_);
v___x_422_ = v_reuseFailAlloc_424_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg___boxed(lean_object* v_hyp_426_, lean_object* v_result_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_426_, v_result_427_);
lean_dec_ref(v_result_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(lean_object* v_hyp_430_, lean_object* v_result_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_430_, v_result_431_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___boxed(lean_object* v_hyp_440_, lean_object* v_result_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(v_hyp_440_, v_result_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec_ref(v_result_441_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object* v_a_450_){
_start:
{
lean_object* v_config_452_; lean_object* v___x_453_; 
v_config_452_ = lean_ctor_get(v_a_450_, 0);
lean_inc_ref(v_config_452_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v_config_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(v_a_454_);
lean_dec_ref(v_a_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_config_469_; lean_object* v___x_470_; 
v_config_469_ = lean_ctor_get(v_a_457_, 0);
lean_inc_ref(v_config_469_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v_config_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(lean_object* v_a_484_){
_start:
{
lean_object* v_restrictedTypes_486_; lean_object* v___x_487_; 
v_restrictedTypes_486_ = lean_ctor_get(v_a_484_, 1);
lean_inc(v_restrictedTypes_486_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_restrictedTypes_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg___boxed(lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___redArg(v_a_488_);
lean_dec_ref(v_a_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_restrictedTypes_503_; lean_object* v___x_504_; 
v_restrictedTypes_503_ = lean_ctor_get(v_a_491_, 1);
lean_inc(v_restrictedTypes_503_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v_restrictedTypes_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes___boxed(lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getRestrictedTypes(v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(lean_object* v_a_518_){
_start:
{
lean_object* v___x_520_; lean_object* v_target_521_; lean_object* v___x_522_; 
v___x_520_ = lean_st_ref_get(v_a_518_);
v_target_521_ = lean_ctor_get(v___x_520_, 4);
lean_inc_ref(v_target_521_);
lean_dec(v___x_520_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v_target_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg___boxed(lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___redArg(v_a_523_);
lean_dec(v_a_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; lean_object* v_target_539_; lean_object* v___x_540_; 
v___x_538_ = lean_st_ref_get(v_a_527_);
v_target_539_ = lean_ctor_get(v___x_538_, 4);
lean_inc_ref(v_target_539_);
lean_dec(v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v_target_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget___boxed(lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTarget(v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(lean_object* v_a_554_){
_start:
{
lean_object* v___x_556_; lean_object* v_target_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_556_ = lean_st_ref_get(v_a_554_);
v_target_557_ = lean_ctor_get(v___x_556_, 4);
lean_inc_ref(v_target_557_);
lean_dec(v___x_556_);
v___x_558_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_557_);
lean_dec_ref(v_target_557_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg___boxed(lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___redArg(v_a_560_);
lean_dec(v_a_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_575_; lean_object* v_target_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = lean_st_ref_get(v_a_564_);
v_target_576_ = lean_ctor_get(v___x_575_, 4);
lean_inc_ref(v_target_576_);
lean_dec(v___x_575_);
v___x_577_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_576_);
lean_dec_ref(v_target_576_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___boxed(lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId(v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(lean_object* v_target_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; lean_object* v_rewriteSimpCache_596_; lean_object* v_rewriteDSimpCache_597_; lean_object* v_acCache_598_; lean_object* v_typeAnalysis_599_; lean_object* v_hypotheses_600_; uint8_t v_didChange_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_611_; 
v___x_595_ = lean_st_ref_take(v_a_593_);
v_rewriteSimpCache_596_ = lean_ctor_get(v___x_595_, 0);
v_rewriteDSimpCache_597_ = lean_ctor_get(v___x_595_, 1);
v_acCache_598_ = lean_ctor_get(v___x_595_, 2);
v_typeAnalysis_599_ = lean_ctor_get(v___x_595_, 3);
v_hypotheses_600_ = lean_ctor_get(v___x_595_, 5);
v_didChange_601_ = lean_ctor_get_uint8(v___x_595_, sizeof(void*)*6);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v___x_595_, 4);
lean_dec(v_unused_612_);
v___x_603_ = v___x_595_;
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_hypotheses_600_);
lean_inc(v_typeAnalysis_599_);
lean_inc(v_acCache_598_);
lean_inc(v_rewriteDSimpCache_597_);
lean_inc(v_rewriteSimpCache_596_);
lean_dec(v___x_595_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 4, v_target_592_);
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_rewriteSimpCache_596_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_rewriteDSimpCache_597_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_acCache_598_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v_typeAnalysis_599_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v_target_592_);
lean_ctor_set(v_reuseFailAlloc_610_, 5, v_hypotheses_600_);
lean_ctor_set_uint8(v_reuseFailAlloc_610_, sizeof(void*)*6, v_didChange_601_);
v___x_606_ = v_reuseFailAlloc_610_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_st_ref_set(v_a_593_, v___x_606_);
v___x_608_ = lean_box(0);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg___boxed(lean_object* v_target_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___redArg(v_target_613_, v_a_614_);
lean_dec(v_a_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(lean_object* v_target_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_630_; lean_object* v_rewriteSimpCache_631_; lean_object* v_rewriteDSimpCache_632_; lean_object* v_acCache_633_; lean_object* v_typeAnalysis_634_; lean_object* v_hypotheses_635_; uint8_t v_didChange_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_646_; 
v___x_630_ = lean_st_ref_take(v_a_619_);
v_rewriteSimpCache_631_ = lean_ctor_get(v___x_630_, 0);
v_rewriteDSimpCache_632_ = lean_ctor_get(v___x_630_, 1);
v_acCache_633_ = lean_ctor_get(v___x_630_, 2);
v_typeAnalysis_634_ = lean_ctor_get(v___x_630_, 3);
v_hypotheses_635_ = lean_ctor_get(v___x_630_, 5);
v_didChange_636_ = lean_ctor_get_uint8(v___x_630_, sizeof(void*)*6);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; 
v_unused_647_ = lean_ctor_get(v___x_630_, 4);
lean_dec(v_unused_647_);
v___x_638_ = v___x_630_;
v_isShared_639_ = v_isSharedCheck_646_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_hypotheses_635_);
lean_inc(v_typeAnalysis_634_);
lean_inc(v_acCache_633_);
lean_inc(v_rewriteDSimpCache_632_);
lean_inc(v_rewriteSimpCache_631_);
lean_dec(v___x_630_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_646_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 4, v_target_617_);
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_rewriteSimpCache_631_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_rewriteDSimpCache_632_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_acCache_633_);
lean_ctor_set(v_reuseFailAlloc_645_, 3, v_typeAnalysis_634_);
lean_ctor_set(v_reuseFailAlloc_645_, 4, v_target_617_);
lean_ctor_set(v_reuseFailAlloc_645_, 5, v_hypotheses_635_);
lean_ctor_set_uint8(v_reuseFailAlloc_645_, sizeof(void*)*6, v_didChange_636_);
v___x_641_ = v_reuseFailAlloc_645_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_st_ref_set(v_a_619_, v___x_641_);
v___x_643_ = lean_box(0);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget___boxed(lean_object* v_target_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setTarget(v_target_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(lean_object* v_a_662_){
_start:
{
lean_object* v___x_664_; uint8_t v_didChange_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_664_ = lean_st_ref_get(v_a_662_);
v_didChange_665_ = lean_ctor_get_uint8(v___x_664_, sizeof(void*)*6);
lean_dec(v___x_664_);
v___x_666_ = lean_box(v_didChange_665_);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg___boxed(lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(v_a_668_);
lean_dec(v_a_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v___x_683_; uint8_t v_didChange_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = lean_st_ref_get(v_a_672_);
v_didChange_684_ = lean_ctor_get_uint8(v___x_683_, sizeof(void*)*6);
lean_dec(v___x_683_);
v___x_685_ = lean_box(v_didChange_684_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___boxed(lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(lean_object* v_a_700_){
_start:
{
lean_object* v___x_702_; lean_object* v_rewriteSimpCache_703_; lean_object* v_rewriteDSimpCache_704_; lean_object* v_acCache_705_; lean_object* v_typeAnalysis_706_; lean_object* v_target_707_; lean_object* v_hypotheses_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_719_; 
v___x_702_ = lean_st_ref_take(v_a_700_);
v_rewriteSimpCache_703_ = lean_ctor_get(v___x_702_, 0);
v_rewriteDSimpCache_704_ = lean_ctor_get(v___x_702_, 1);
v_acCache_705_ = lean_ctor_get(v___x_702_, 2);
v_typeAnalysis_706_ = lean_ctor_get(v___x_702_, 3);
v_target_707_ = lean_ctor_get(v___x_702_, 4);
v_hypotheses_708_ = lean_ctor_get(v___x_702_, 5);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_719_ == 0)
{
v___x_710_ = v___x_702_;
v_isShared_711_ = v_isSharedCheck_719_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_hypotheses_708_);
lean_inc(v_target_707_);
lean_inc(v_typeAnalysis_706_);
lean_inc(v_acCache_705_);
lean_inc(v_rewriteDSimpCache_704_);
lean_inc(v_rewriteSimpCache_703_);
lean_dec(v___x_702_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_719_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
uint8_t v___x_712_; lean_object* v___x_714_; 
v___x_712_ = 0;
if (v_isShared_711_ == 0)
{
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_rewriteSimpCache_703_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_rewriteDSimpCache_704_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_acCache_705_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_typeAnalysis_706_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_target_707_);
lean_ctor_set(v_reuseFailAlloc_718_, 5, v_hypotheses_708_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_ctor_set_uint8(v___x_714_, sizeof(void*)*6, v___x_712_);
v___x_715_ = lean_st_ref_set(v_a_700_, v___x_714_);
v___x_716_ = lean_box(0);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg___boxed(lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(v_a_720_);
lean_dec(v_a_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; lean_object* v_rewriteSimpCache_736_; lean_object* v_rewriteDSimpCache_737_; lean_object* v_acCache_738_; lean_object* v_typeAnalysis_739_; lean_object* v_target_740_; lean_object* v_hypotheses_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_752_; 
v___x_735_ = lean_st_ref_take(v_a_724_);
v_rewriteSimpCache_736_ = lean_ctor_get(v___x_735_, 0);
v_rewriteDSimpCache_737_ = lean_ctor_get(v___x_735_, 1);
v_acCache_738_ = lean_ctor_get(v___x_735_, 2);
v_typeAnalysis_739_ = lean_ctor_get(v___x_735_, 3);
v_target_740_ = lean_ctor_get(v___x_735_, 4);
v_hypotheses_741_ = lean_ctor_get(v___x_735_, 5);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_752_ == 0)
{
v___x_743_ = v___x_735_;
v_isShared_744_ = v_isSharedCheck_752_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_hypotheses_741_);
lean_inc(v_target_740_);
lean_inc(v_typeAnalysis_739_);
lean_inc(v_acCache_738_);
lean_inc(v_rewriteDSimpCache_737_);
lean_inc(v_rewriteSimpCache_736_);
lean_dec(v___x_735_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_752_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
uint8_t v___x_745_; lean_object* v___x_747_; 
v___x_745_ = 0;
if (v_isShared_744_ == 0)
{
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_rewriteSimpCache_736_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_rewriteDSimpCache_737_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_acCache_738_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_typeAnalysis_739_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v_target_740_);
lean_ctor_set(v_reuseFailAlloc_751_, 5, v_hypotheses_741_);
v___x_747_ = v_reuseFailAlloc_751_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*6, v___x_745_);
v___x_748_ = lean_st_ref_set(v_a_724_, v___x_747_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___boxed(lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(lean_object* v_a_766_){
_start:
{
lean_object* v___x_768_; lean_object* v_rewriteSimpCache_769_; lean_object* v_rewriteDSimpCache_770_; lean_object* v_acCache_771_; lean_object* v_typeAnalysis_772_; lean_object* v_target_773_; lean_object* v_hypotheses_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_785_; 
v___x_768_ = lean_st_ref_take(v_a_766_);
v_rewriteSimpCache_769_ = lean_ctor_get(v___x_768_, 0);
v_rewriteDSimpCache_770_ = lean_ctor_get(v___x_768_, 1);
v_acCache_771_ = lean_ctor_get(v___x_768_, 2);
v_typeAnalysis_772_ = lean_ctor_get(v___x_768_, 3);
v_target_773_ = lean_ctor_get(v___x_768_, 4);
v_hypotheses_774_ = lean_ctor_get(v___x_768_, 5);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_785_ == 0)
{
v___x_776_ = v___x_768_;
v_isShared_777_ = v_isSharedCheck_785_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_hypotheses_774_);
lean_inc(v_target_773_);
lean_inc(v_typeAnalysis_772_);
lean_inc(v_acCache_771_);
lean_inc(v_rewriteDSimpCache_770_);
lean_inc(v_rewriteSimpCache_769_);
lean_dec(v___x_768_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_785_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
uint8_t v___x_778_; lean_object* v___x_780_; 
v___x_778_ = 1;
if (v_isShared_777_ == 0)
{
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_rewriteSimpCache_769_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_rewriteDSimpCache_770_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_acCache_771_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_typeAnalysis_772_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_target_773_);
lean_ctor_set(v_reuseFailAlloc_784_, 5, v_hypotheses_774_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*6, v___x_778_);
v___x_781_ = lean_st_ref_set(v_a_766_, v___x_780_);
v___x_782_ = lean_box(0);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg___boxed(lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(v_a_786_);
lean_dec(v_a_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_801_; lean_object* v_rewriteSimpCache_802_; lean_object* v_rewriteDSimpCache_803_; lean_object* v_acCache_804_; lean_object* v_typeAnalysis_805_; lean_object* v_target_806_; lean_object* v_hypotheses_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_818_; 
v___x_801_ = lean_st_ref_take(v_a_790_);
v_rewriteSimpCache_802_ = lean_ctor_get(v___x_801_, 0);
v_rewriteDSimpCache_803_ = lean_ctor_get(v___x_801_, 1);
v_acCache_804_ = lean_ctor_get(v___x_801_, 2);
v_typeAnalysis_805_ = lean_ctor_get(v___x_801_, 3);
v_target_806_ = lean_ctor_get(v___x_801_, 4);
v_hypotheses_807_ = lean_ctor_get(v___x_801_, 5);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_818_ == 0)
{
v___x_809_ = v___x_801_;
v_isShared_810_ = v_isSharedCheck_818_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_hypotheses_807_);
lean_inc(v_target_806_);
lean_inc(v_typeAnalysis_805_);
lean_inc(v_acCache_804_);
lean_inc(v_rewriteDSimpCache_803_);
lean_inc(v_rewriteSimpCache_802_);
lean_dec(v___x_801_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_818_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
uint8_t v___x_811_; lean_object* v___x_813_; 
v___x_811_ = 1;
if (v_isShared_810_ == 0)
{
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_rewriteSimpCache_802_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_rewriteDSimpCache_803_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_acCache_804_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v_typeAnalysis_805_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v_target_806_);
lean_ctor_set(v_reuseFailAlloc_817_, 5, v_hypotheses_807_);
v___x_813_ = v_reuseFailAlloc_817_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*6, v___x_811_);
v___x_814_ = lean_st_ref_set(v_a_790_, v___x_813_);
v___x_815_ = lean_box(0);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed(lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
return v_res_831_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0(void){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_832_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg(lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; lean_object* v_rewriteSimpCache_838_; lean_object* v_rewriteDSimpCache_839_; lean_object* v_acCache_840_; lean_object* v_typeAnalysis_841_; lean_object* v_target_842_; lean_object* v_hypotheses_843_; uint8_t v_didChange_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_854_; 
v___x_837_ = lean_st_ref_take(v_a_835_);
v_rewriteSimpCache_838_ = lean_ctor_get(v___x_837_, 0);
v_rewriteDSimpCache_839_ = lean_ctor_get(v___x_837_, 1);
v_acCache_840_ = lean_ctor_get(v___x_837_, 2);
v_typeAnalysis_841_ = lean_ctor_get(v___x_837_, 3);
v_target_842_ = lean_ctor_get(v___x_837_, 4);
v_hypotheses_843_ = lean_ctor_get(v___x_837_, 5);
v_didChange_844_ = lean_ctor_get_uint8(v___x_837_, sizeof(void*)*6);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_854_ == 0)
{
v___x_846_ = v___x_837_;
v_isShared_847_ = v_isSharedCheck_854_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_hypotheses_843_);
lean_inc(v_target_842_);
lean_inc(v_typeAnalysis_841_);
lean_inc(v_acCache_840_);
lean_inc(v_rewriteDSimpCache_839_);
lean_inc(v_rewriteSimpCache_838_);
lean_dec(v___x_837_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_854_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_848_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_848_);
v___x_850_ = v___x_846_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_rewriteDSimpCache_839_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v_acCache_840_);
lean_ctor_set(v_reuseFailAlloc_853_, 3, v_typeAnalysis_841_);
lean_ctor_set(v_reuseFailAlloc_853_, 4, v_target_842_);
lean_ctor_set(v_reuseFailAlloc_853_, 5, v_hypotheses_843_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, sizeof(void*)*6, v_didChange_844_);
v___x_850_ = v_reuseFailAlloc_853_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_st_ref_set(v_a_835_, v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v_rewriteSimpCache_838_);
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___boxed(lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg(v_a_855_);
lean_dec(v_a_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache(lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; lean_object* v_rewriteSimpCache_871_; lean_object* v_rewriteDSimpCache_872_; lean_object* v_acCache_873_; lean_object* v_typeAnalysis_874_; lean_object* v_target_875_; lean_object* v_hypotheses_876_; uint8_t v_didChange_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_887_; 
v___x_870_ = lean_st_ref_take(v_a_859_);
v_rewriteSimpCache_871_ = lean_ctor_get(v___x_870_, 0);
v_rewriteDSimpCache_872_ = lean_ctor_get(v___x_870_, 1);
v_acCache_873_ = lean_ctor_get(v___x_870_, 2);
v_typeAnalysis_874_ = lean_ctor_get(v___x_870_, 3);
v_target_875_ = lean_ctor_get(v___x_870_, 4);
v_hypotheses_876_ = lean_ctor_get(v___x_870_, 5);
v_didChange_877_ = lean_ctor_get_uint8(v___x_870_, sizeof(void*)*6);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_887_ == 0)
{
v___x_879_ = v___x_870_;
v_isShared_880_ = v_isSharedCheck_887_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_hypotheses_876_);
lean_inc(v_target_875_);
lean_inc(v_typeAnalysis_874_);
lean_inc(v_acCache_873_);
lean_inc(v_rewriteDSimpCache_872_);
lean_inc(v_rewriteSimpCache_871_);
lean_dec(v___x_870_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_887_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_881_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_rewriteDSimpCache_872_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_acCache_873_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v_typeAnalysis_874_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v_target_875_);
lean_ctor_set(v_reuseFailAlloc_886_, 5, v_hypotheses_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_886_, sizeof(void*)*6, v_didChange_877_);
v___x_883_ = v_reuseFailAlloc_886_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_st_ref_set(v_a_859_, v___x_883_);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v_rewriteSimpCache_871_);
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___boxed(lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache(v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg(lean_object* v_cache_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_904_; lean_object* v_rewriteDSimpCache_905_; lean_object* v_acCache_906_; lean_object* v_typeAnalysis_907_; lean_object* v_target_908_; lean_object* v_hypotheses_909_; uint8_t v_didChange_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_920_; 
v___x_904_ = lean_st_ref_take(v_a_902_);
v_rewriteDSimpCache_905_ = lean_ctor_get(v___x_904_, 1);
v_acCache_906_ = lean_ctor_get(v___x_904_, 2);
v_typeAnalysis_907_ = lean_ctor_get(v___x_904_, 3);
v_target_908_ = lean_ctor_get(v___x_904_, 4);
v_hypotheses_909_ = lean_ctor_get(v___x_904_, 5);
v_didChange_910_ = lean_ctor_get_uint8(v___x_904_, sizeof(void*)*6);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v___x_904_, 0);
lean_dec(v_unused_921_);
v___x_912_ = v___x_904_;
v_isShared_913_ = v_isSharedCheck_920_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_hypotheses_909_);
lean_inc(v_target_908_);
lean_inc(v_typeAnalysis_907_);
lean_inc(v_acCache_906_);
lean_inc(v_rewriteDSimpCache_905_);
lean_dec(v___x_904_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_920_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v_cache_901_);
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_cache_901_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_rewriteDSimpCache_905_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_acCache_906_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_typeAnalysis_907_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_target_908_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v_hypotheses_909_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*6, v_didChange_910_);
v___x_915_ = v_reuseFailAlloc_919_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_st_ref_set(v_a_902_, v___x_915_);
v___x_917_ = lean_box(0);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg___boxed(lean_object* v_cache_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg(v_cache_922_, v_a_923_);
lean_dec(v_a_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache(lean_object* v_cache_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___x_939_; lean_object* v_rewriteDSimpCache_940_; lean_object* v_acCache_941_; lean_object* v_typeAnalysis_942_; lean_object* v_target_943_; lean_object* v_hypotheses_944_; uint8_t v_didChange_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_955_; 
v___x_939_ = lean_st_ref_take(v_a_928_);
v_rewriteDSimpCache_940_ = lean_ctor_get(v___x_939_, 1);
v_acCache_941_ = lean_ctor_get(v___x_939_, 2);
v_typeAnalysis_942_ = lean_ctor_get(v___x_939_, 3);
v_target_943_ = lean_ctor_get(v___x_939_, 4);
v_hypotheses_944_ = lean_ctor_get(v___x_939_, 5);
v_didChange_945_ = lean_ctor_get_uint8(v___x_939_, sizeof(void*)*6);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v___x_939_, 0);
lean_dec(v_unused_956_);
v___x_947_ = v___x_939_;
v_isShared_948_ = v_isSharedCheck_955_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_hypotheses_944_);
lean_inc(v_target_943_);
lean_inc(v_typeAnalysis_942_);
lean_inc(v_acCache_941_);
lean_inc(v_rewriteDSimpCache_940_);
lean_dec(v___x_939_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_955_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v_cache_926_);
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_cache_926_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_rewriteDSimpCache_940_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_acCache_941_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_typeAnalysis_942_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v_target_943_);
lean_ctor_set(v_reuseFailAlloc_954_, 5, v_hypotheses_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*6, v_didChange_945_);
v___x_950_ = v_reuseFailAlloc_954_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_st_ref_set(v_a_928_, v___x_950_);
v___x_952_ = lean_box(0);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___boxed(lean_object* v_cache_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache(v_cache_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg(lean_object* v_a_971_){
_start:
{
lean_object* v___x_973_; lean_object* v_rewriteDSimpCache_974_; lean_object* v_acCache_975_; lean_object* v_typeAnalysis_976_; lean_object* v_target_977_; lean_object* v_hypotheses_978_; uint8_t v_didChange_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_990_; 
v___x_973_ = lean_st_ref_take(v_a_971_);
v_rewriteDSimpCache_974_ = lean_ctor_get(v___x_973_, 1);
v_acCache_975_ = lean_ctor_get(v___x_973_, 2);
v_typeAnalysis_976_ = lean_ctor_get(v___x_973_, 3);
v_target_977_ = lean_ctor_get(v___x_973_, 4);
v_hypotheses_978_ = lean_ctor_get(v___x_973_, 5);
v_didChange_979_ = lean_ctor_get_uint8(v___x_973_, sizeof(void*)*6);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v___x_973_, 0);
lean_dec(v_unused_991_);
v___x_981_ = v___x_973_;
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_hypotheses_978_);
lean_inc(v_target_977_);
lean_inc(v_typeAnalysis_976_);
lean_inc(v_acCache_975_);
lean_inc(v_rewriteDSimpCache_974_);
lean_dec(v___x_973_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_rewriteDSimpCache_974_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_acCache_975_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v_typeAnalysis_976_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v_target_977_);
lean_ctor_set(v_reuseFailAlloc_989_, 5, v_hypotheses_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_989_, sizeof(void*)*6, v_didChange_979_);
v___x_985_ = v_reuseFailAlloc_989_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = lean_st_ref_set(v_a_971_, v___x_985_);
v___x_987_ = lean_box(0);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg___boxed(lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg(v_a_992_);
lean_dec(v_a_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache(lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v_rewriteDSimpCache_1008_; lean_object* v_acCache_1009_; lean_object* v_typeAnalysis_1010_; lean_object* v_target_1011_; lean_object* v_hypotheses_1012_; uint8_t v_didChange_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1024_; 
v___x_1007_ = lean_st_ref_take(v_a_996_);
v_rewriteDSimpCache_1008_ = lean_ctor_get(v___x_1007_, 1);
v_acCache_1009_ = lean_ctor_get(v___x_1007_, 2);
v_typeAnalysis_1010_ = lean_ctor_get(v___x_1007_, 3);
v_target_1011_ = lean_ctor_get(v___x_1007_, 4);
v_hypotheses_1012_ = lean_ctor_get(v___x_1007_, 5);
v_didChange_1013_ = lean_ctor_get_uint8(v___x_1007_, sizeof(void*)*6);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v___x_1007_, 0);
lean_dec(v_unused_1025_);
v___x_1015_ = v___x_1007_;
v_isShared_1016_ = v_isSharedCheck_1024_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_hypotheses_1012_);
lean_inc(v_target_1011_);
lean_inc(v_typeAnalysis_1010_);
lean_inc(v_acCache_1009_);
lean_inc(v_rewriteDSimpCache_1008_);
lean_dec(v___x_1007_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1024_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1017_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1017_);
v___x_1019_ = v___x_1015_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_rewriteDSimpCache_1008_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_acCache_1009_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v_typeAnalysis_1010_);
lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_target_1011_);
lean_ctor_set(v_reuseFailAlloc_1023_, 5, v_hypotheses_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1023_, sizeof(void*)*6, v_didChange_1013_);
v___x_1019_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = lean_st_ref_set(v_a_996_, v___x_1019_);
v___x_1021_ = lean_box(0);
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
return v___x_1022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___boxed(lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache(v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
return v_res_1038_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0(void){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg(lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1044_; lean_object* v_rewriteSimpCache_1045_; lean_object* v_rewriteDSimpCache_1046_; lean_object* v_acCache_1047_; lean_object* v_typeAnalysis_1048_; lean_object* v_target_1049_; lean_object* v_hypotheses_1050_; uint8_t v_didChange_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1061_; 
v___x_1044_ = lean_st_ref_take(v_a_1042_);
v_rewriteSimpCache_1045_ = lean_ctor_get(v___x_1044_, 0);
v_rewriteDSimpCache_1046_ = lean_ctor_get(v___x_1044_, 1);
v_acCache_1047_ = lean_ctor_get(v___x_1044_, 2);
v_typeAnalysis_1048_ = lean_ctor_get(v___x_1044_, 3);
v_target_1049_ = lean_ctor_get(v___x_1044_, 4);
v_hypotheses_1050_ = lean_ctor_get(v___x_1044_, 5);
v_didChange_1051_ = lean_ctor_get_uint8(v___x_1044_, sizeof(void*)*6);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1053_ = v___x_1044_;
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_hypotheses_1050_);
lean_inc(v_target_1049_);
lean_inc(v_typeAnalysis_1048_);
lean_inc(v_acCache_1047_);
lean_inc(v_rewriteDSimpCache_1046_);
lean_inc(v_rewriteSimpCache_1045_);
lean_dec(v___x_1044_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_rewriteSimpCache_1045_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_acCache_1047_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v_typeAnalysis_1048_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v_target_1049_);
lean_ctor_set(v_reuseFailAlloc_1060_, 5, v_hypotheses_1050_);
lean_ctor_set_uint8(v_reuseFailAlloc_1060_, sizeof(void*)*6, v_didChange_1051_);
v___x_1057_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_st_ref_set(v_a_1042_, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_rewriteDSimpCache_1046_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___boxed(lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg(v_a_1062_);
lean_dec(v_a_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache(lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v___x_1077_; lean_object* v_rewriteSimpCache_1078_; lean_object* v_rewriteDSimpCache_1079_; lean_object* v_acCache_1080_; lean_object* v_typeAnalysis_1081_; lean_object* v_target_1082_; lean_object* v_hypotheses_1083_; uint8_t v_didChange_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1094_; 
v___x_1077_ = lean_st_ref_take(v_a_1066_);
v_rewriteSimpCache_1078_ = lean_ctor_get(v___x_1077_, 0);
v_rewriteDSimpCache_1079_ = lean_ctor_get(v___x_1077_, 1);
v_acCache_1080_ = lean_ctor_get(v___x_1077_, 2);
v_typeAnalysis_1081_ = lean_ctor_get(v___x_1077_, 3);
v_target_1082_ = lean_ctor_get(v___x_1077_, 4);
v_hypotheses_1083_ = lean_ctor_get(v___x_1077_, 5);
v_didChange_1084_ = lean_ctor_get_uint8(v___x_1077_, sizeof(void*)*6);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1086_ = v___x_1077_;
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_hypotheses_1083_);
lean_inc(v_target_1082_);
lean_inc(v_typeAnalysis_1081_);
lean_inc(v_acCache_1080_);
lean_inc(v_rewriteDSimpCache_1079_);
lean_inc(v_rewriteSimpCache_1078_);
lean_dec(v___x_1077_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 1, v___x_1088_);
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_rewriteSimpCache_1078_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_acCache_1080_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v_typeAnalysis_1081_);
lean_ctor_set(v_reuseFailAlloc_1093_, 4, v_target_1082_);
lean_ctor_set(v_reuseFailAlloc_1093_, 5, v_hypotheses_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1093_, sizeof(void*)*6, v_didChange_1084_);
v___x_1090_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_st_ref_set(v_a_1066_, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_rewriteDSimpCache_1079_);
return v___x_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___boxed(lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache(v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg(lean_object* v_cache_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_rewriteSimpCache_1112_; lean_object* v_acCache_1113_; lean_object* v_typeAnalysis_1114_; lean_object* v_target_1115_; lean_object* v_hypotheses_1116_; uint8_t v_didChange_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1127_; 
v___x_1111_ = lean_st_ref_take(v_a_1109_);
v_rewriteSimpCache_1112_ = lean_ctor_get(v___x_1111_, 0);
v_acCache_1113_ = lean_ctor_get(v___x_1111_, 2);
v_typeAnalysis_1114_ = lean_ctor_get(v___x_1111_, 3);
v_target_1115_ = lean_ctor_get(v___x_1111_, 4);
v_hypotheses_1116_ = lean_ctor_get(v___x_1111_, 5);
v_didChange_1117_ = lean_ctor_get_uint8(v___x_1111_, sizeof(void*)*6);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v___x_1111_, 1);
lean_dec(v_unused_1128_);
v___x_1119_ = v___x_1111_;
v_isShared_1120_ = v_isSharedCheck_1127_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_hypotheses_1116_);
lean_inc(v_target_1115_);
lean_inc(v_typeAnalysis_1114_);
lean_inc(v_acCache_1113_);
lean_inc(v_rewriteSimpCache_1112_);
lean_dec(v___x_1111_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1127_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 1, v_cache_1108_);
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_rewriteSimpCache_1112_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_cache_1108_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_acCache_1113_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_typeAnalysis_1114_);
lean_ctor_set(v_reuseFailAlloc_1126_, 4, v_target_1115_);
lean_ctor_set(v_reuseFailAlloc_1126_, 5, v_hypotheses_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*6, v_didChange_1117_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = lean_st_ref_set(v_a_1109_, v___x_1122_);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
return v___x_1125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg___boxed(lean_object* v_cache_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg(v_cache_1129_, v_a_1130_);
lean_dec(v_a_1130_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache(lean_object* v_cache_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v___x_1146_; lean_object* v_rewriteSimpCache_1147_; lean_object* v_acCache_1148_; lean_object* v_typeAnalysis_1149_; lean_object* v_target_1150_; lean_object* v_hypotheses_1151_; uint8_t v_didChange_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1162_; 
v___x_1146_ = lean_st_ref_take(v_a_1135_);
v_rewriteSimpCache_1147_ = lean_ctor_get(v___x_1146_, 0);
v_acCache_1148_ = lean_ctor_get(v___x_1146_, 2);
v_typeAnalysis_1149_ = lean_ctor_get(v___x_1146_, 3);
v_target_1150_ = lean_ctor_get(v___x_1146_, 4);
v_hypotheses_1151_ = lean_ctor_get(v___x_1146_, 5);
v_didChange_1152_ = lean_ctor_get_uint8(v___x_1146_, sizeof(void*)*6);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; 
v_unused_1163_ = lean_ctor_get(v___x_1146_, 1);
lean_dec(v_unused_1163_);
v___x_1154_ = v___x_1146_;
v_isShared_1155_ = v_isSharedCheck_1162_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_hypotheses_1151_);
lean_inc(v_target_1150_);
lean_inc(v_typeAnalysis_1149_);
lean_inc(v_acCache_1148_);
lean_inc(v_rewriteSimpCache_1147_);
lean_dec(v___x_1146_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1162_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_cache_1133_);
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_rewriteSimpCache_1147_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_cache_1133_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_acCache_1148_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_typeAnalysis_1149_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_target_1150_);
lean_ctor_set(v_reuseFailAlloc_1161_, 5, v_hypotheses_1151_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*6, v_didChange_1152_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_st_ref_set(v_a_1135_, v___x_1157_);
v___x_1159_ = lean_box(0);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___boxed(lean_object* v_cache_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache(v_cache_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg(lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v_rewriteSimpCache_1181_; lean_object* v_acCache_1182_; lean_object* v_typeAnalysis_1183_; lean_object* v_target_1184_; lean_object* v_hypotheses_1185_; uint8_t v_didChange_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1197_; 
v___x_1180_ = lean_st_ref_take(v_a_1178_);
v_rewriteSimpCache_1181_ = lean_ctor_get(v___x_1180_, 0);
v_acCache_1182_ = lean_ctor_get(v___x_1180_, 2);
v_typeAnalysis_1183_ = lean_ctor_get(v___x_1180_, 3);
v_target_1184_ = lean_ctor_get(v___x_1180_, 4);
v_hypotheses_1185_ = lean_ctor_get(v___x_1180_, 5);
v_didChange_1186_ = lean_ctor_get_uint8(v___x_1180_, sizeof(void*)*6);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v___x_1180_, 1);
lean_dec(v_unused_1198_);
v___x_1188_ = v___x_1180_;
v_isShared_1189_ = v_isSharedCheck_1197_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_hypotheses_1185_);
lean_inc(v_target_1184_);
lean_inc(v_typeAnalysis_1183_);
lean_inc(v_acCache_1182_);
lean_inc(v_rewriteSimpCache_1181_);
lean_dec(v___x_1180_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1197_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_rewriteSimpCache_1181_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_acCache_1182_);
lean_ctor_set(v_reuseFailAlloc_1196_, 3, v_typeAnalysis_1183_);
lean_ctor_set(v_reuseFailAlloc_1196_, 4, v_target_1184_);
lean_ctor_set(v_reuseFailAlloc_1196_, 5, v_hypotheses_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*6, v_didChange_1186_);
v___x_1192_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1193_ = lean_st_ref_set(v_a_1178_, v___x_1192_);
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg___boxed(lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg(v_a_1199_);
lean_dec(v_a_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache(lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v___x_1214_; lean_object* v_rewriteSimpCache_1215_; lean_object* v_acCache_1216_; lean_object* v_typeAnalysis_1217_; lean_object* v_target_1218_; lean_object* v_hypotheses_1219_; uint8_t v_didChange_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1231_; 
v___x_1214_ = lean_st_ref_take(v_a_1203_);
v_rewriteSimpCache_1215_ = lean_ctor_get(v___x_1214_, 0);
v_acCache_1216_ = lean_ctor_get(v___x_1214_, 2);
v_typeAnalysis_1217_ = lean_ctor_get(v___x_1214_, 3);
v_target_1218_ = lean_ctor_get(v___x_1214_, 4);
v_hypotheses_1219_ = lean_ctor_get(v___x_1214_, 5);
v_didChange_1220_ = lean_ctor_get_uint8(v___x_1214_, sizeof(void*)*6);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v___x_1214_, 1);
lean_dec(v_unused_1232_);
v___x_1222_ = v___x_1214_;
v_isShared_1223_ = v_isSharedCheck_1231_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_hypotheses_1219_);
lean_inc(v_target_1218_);
lean_inc(v_typeAnalysis_1217_);
lean_inc(v_acCache_1216_);
lean_inc(v_rewriteSimpCache_1215_);
lean_dec(v___x_1214_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1231_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1224_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 1, v___x_1224_);
v___x_1226_ = v___x_1222_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_rewriteSimpCache_1215_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_acCache_1216_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_typeAnalysis_1217_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_target_1218_);
lean_ctor_set(v_reuseFailAlloc_1230_, 5, v_hypotheses_1219_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, sizeof(void*)*6, v_didChange_1220_);
v___x_1226_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = lean_st_ref_set(v_a_1203_, v___x_1226_);
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___boxed(lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache(v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg(lean_object* v_a_1246_){
_start:
{
lean_object* v___x_1248_; lean_object* v_rewriteSimpCache_1249_; lean_object* v_rewriteDSimpCache_1250_; lean_object* v_acCache_1251_; lean_object* v_typeAnalysis_1252_; lean_object* v_target_1253_; lean_object* v_hypotheses_1254_; uint8_t v_didChange_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1265_; 
v___x_1248_ = lean_st_ref_take(v_a_1246_);
v_rewriteSimpCache_1249_ = lean_ctor_get(v___x_1248_, 0);
v_rewriteDSimpCache_1250_ = lean_ctor_get(v___x_1248_, 1);
v_acCache_1251_ = lean_ctor_get(v___x_1248_, 2);
v_typeAnalysis_1252_ = lean_ctor_get(v___x_1248_, 3);
v_target_1253_ = lean_ctor_get(v___x_1248_, 4);
v_hypotheses_1254_ = lean_ctor_get(v___x_1248_, 5);
v_didChange_1255_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*6);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1257_ = v___x_1248_;
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_hypotheses_1254_);
lean_inc(v_target_1253_);
lean_inc(v_typeAnalysis_1252_);
lean_inc(v_acCache_1251_);
lean_inc(v_rewriteDSimpCache_1250_);
lean_inc(v_rewriteSimpCache_1249_);
lean_dec(v___x_1248_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 2, v___x_1259_);
v___x_1261_ = v___x_1257_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_rewriteSimpCache_1249_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_rewriteDSimpCache_1250_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_typeAnalysis_1252_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v_target_1253_);
lean_ctor_set(v_reuseFailAlloc_1264_, 5, v_hypotheses_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1264_, sizeof(void*)*6, v_didChange_1255_);
v___x_1261_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_st_ref_set(v_a_1246_, v___x_1261_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_acCache_1251_);
return v___x_1263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg___boxed(lean_object* v_a_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg(v_a_1266_);
lean_dec(v_a_1266_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache(lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v___x_1281_; lean_object* v_rewriteSimpCache_1282_; lean_object* v_rewriteDSimpCache_1283_; lean_object* v_acCache_1284_; lean_object* v_typeAnalysis_1285_; lean_object* v_target_1286_; lean_object* v_hypotheses_1287_; uint8_t v_didChange_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1298_; 
v___x_1281_ = lean_st_ref_take(v_a_1270_);
v_rewriteSimpCache_1282_ = lean_ctor_get(v___x_1281_, 0);
v_rewriteDSimpCache_1283_ = lean_ctor_get(v___x_1281_, 1);
v_acCache_1284_ = lean_ctor_get(v___x_1281_, 2);
v_typeAnalysis_1285_ = lean_ctor_get(v___x_1281_, 3);
v_target_1286_ = lean_ctor_get(v___x_1281_, 4);
v_hypotheses_1287_ = lean_ctor_get(v___x_1281_, 5);
v_didChange_1288_ = lean_ctor_get_uint8(v___x_1281_, sizeof(void*)*6);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1290_ = v___x_1281_;
v_isShared_1291_ = v_isSharedCheck_1298_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_hypotheses_1287_);
lean_inc(v_target_1286_);
lean_inc(v_typeAnalysis_1285_);
lean_inc(v_acCache_1284_);
lean_inc(v_rewriteDSimpCache_1283_);
lean_inc(v_rewriteSimpCache_1282_);
lean_dec(v___x_1281_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1298_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1292_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 2, v___x_1292_);
v___x_1294_ = v___x_1290_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_rewriteSimpCache_1282_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_rewriteDSimpCache_1283_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1297_, 3, v_typeAnalysis_1285_);
lean_ctor_set(v_reuseFailAlloc_1297_, 4, v_target_1286_);
lean_ctor_set(v_reuseFailAlloc_1297_, 5, v_hypotheses_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*6, v_didChange_1288_);
v___x_1294_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_st_ref_set(v_a_1270_, v___x_1294_);
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_acCache_1284_);
return v___x_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___boxed(lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache(v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg(lean_object* v_cache_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v___x_1315_; lean_object* v_rewriteSimpCache_1316_; lean_object* v_rewriteDSimpCache_1317_; lean_object* v_typeAnalysis_1318_; lean_object* v_target_1319_; lean_object* v_hypotheses_1320_; uint8_t v_didChange_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1331_; 
v___x_1315_ = lean_st_ref_take(v_a_1313_);
v_rewriteSimpCache_1316_ = lean_ctor_get(v___x_1315_, 0);
v_rewriteDSimpCache_1317_ = lean_ctor_get(v___x_1315_, 1);
v_typeAnalysis_1318_ = lean_ctor_get(v___x_1315_, 3);
v_target_1319_ = lean_ctor_get(v___x_1315_, 4);
v_hypotheses_1320_ = lean_ctor_get(v___x_1315_, 5);
v_didChange_1321_ = lean_ctor_get_uint8(v___x_1315_, sizeof(void*)*6);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v___x_1315_, 2);
lean_dec(v_unused_1332_);
v___x_1323_ = v___x_1315_;
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_hypotheses_1320_);
lean_inc(v_target_1319_);
lean_inc(v_typeAnalysis_1318_);
lean_inc(v_rewriteDSimpCache_1317_);
lean_inc(v_rewriteSimpCache_1316_);
lean_dec(v___x_1315_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 2, v_cache_1312_);
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_rewriteSimpCache_1316_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_rewriteDSimpCache_1317_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_cache_1312_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_typeAnalysis_1318_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v_target_1319_);
lean_ctor_set(v_reuseFailAlloc_1330_, 5, v_hypotheses_1320_);
lean_ctor_set_uint8(v_reuseFailAlloc_1330_, sizeof(void*)*6, v_didChange_1321_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = lean_st_ref_set(v_a_1313_, v___x_1326_);
v___x_1328_ = lean_box(0);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg___boxed(lean_object* v_cache_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg(v_cache_1333_, v_a_1334_);
lean_dec(v_a_1334_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache(lean_object* v_cache_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v_rewriteSimpCache_1351_; lean_object* v_rewriteDSimpCache_1352_; lean_object* v_typeAnalysis_1353_; lean_object* v_target_1354_; lean_object* v_hypotheses_1355_; uint8_t v_didChange_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1366_; 
v___x_1350_ = lean_st_ref_take(v_a_1339_);
v_rewriteSimpCache_1351_ = lean_ctor_get(v___x_1350_, 0);
v_rewriteDSimpCache_1352_ = lean_ctor_get(v___x_1350_, 1);
v_typeAnalysis_1353_ = lean_ctor_get(v___x_1350_, 3);
v_target_1354_ = lean_ctor_get(v___x_1350_, 4);
v_hypotheses_1355_ = lean_ctor_get(v___x_1350_, 5);
v_didChange_1356_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*6);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v___x_1350_, 2);
lean_dec(v_unused_1367_);
v___x_1358_ = v___x_1350_;
v_isShared_1359_ = v_isSharedCheck_1366_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_hypotheses_1355_);
lean_inc(v_target_1354_);
lean_inc(v_typeAnalysis_1353_);
lean_inc(v_rewriteDSimpCache_1352_);
lean_inc(v_rewriteSimpCache_1351_);
lean_dec(v___x_1350_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1366_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 2, v_cache_1337_);
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_rewriteSimpCache_1351_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_rewriteDSimpCache_1352_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_cache_1337_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_typeAnalysis_1353_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_target_1354_);
lean_ctor_set(v_reuseFailAlloc_1365_, 5, v_hypotheses_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*6, v_didChange_1356_);
v___x_1361_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = lean_st_ref_set(v_a_1339_, v___x_1361_);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___boxed(lean_object* v_cache_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache(v_cache_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg(lean_object* v_a_1382_){
_start:
{
lean_object* v___x_1384_; lean_object* v_rewriteSimpCache_1385_; lean_object* v_rewriteDSimpCache_1386_; lean_object* v_typeAnalysis_1387_; lean_object* v_target_1388_; lean_object* v_hypotheses_1389_; uint8_t v_didChange_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1401_; 
v___x_1384_ = lean_st_ref_take(v_a_1382_);
v_rewriteSimpCache_1385_ = lean_ctor_get(v___x_1384_, 0);
v_rewriteDSimpCache_1386_ = lean_ctor_get(v___x_1384_, 1);
v_typeAnalysis_1387_ = lean_ctor_get(v___x_1384_, 3);
v_target_1388_ = lean_ctor_get(v___x_1384_, 4);
v_hypotheses_1389_ = lean_ctor_get(v___x_1384_, 5);
v_didChange_1390_ = lean_ctor_get_uint8(v___x_1384_, sizeof(void*)*6);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v___x_1384_, 2);
lean_dec(v_unused_1402_);
v___x_1392_ = v___x_1384_;
v_isShared_1393_ = v_isSharedCheck_1401_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_hypotheses_1389_);
lean_inc(v_target_1388_);
lean_inc(v_typeAnalysis_1387_);
lean_inc(v_rewriteDSimpCache_1386_);
lean_inc(v_rewriteSimpCache_1385_);
lean_dec(v___x_1384_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1401_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1394_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 2, v___x_1394_);
v___x_1396_ = v___x_1392_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_rewriteSimpCache_1385_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_rewriteDSimpCache_1386_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_typeAnalysis_1387_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_target_1388_);
lean_ctor_set(v_reuseFailAlloc_1400_, 5, v_hypotheses_1389_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*6, v_didChange_1390_);
v___x_1396_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = lean_st_ref_set(v_a_1382_, v___x_1396_);
v___x_1398_ = lean_box(0);
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg___boxed(lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg(v_a_1403_);
lean_dec(v_a_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache(lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v___x_1418_; lean_object* v_rewriteSimpCache_1419_; lean_object* v_rewriteDSimpCache_1420_; lean_object* v_typeAnalysis_1421_; lean_object* v_target_1422_; lean_object* v_hypotheses_1423_; uint8_t v_didChange_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1435_; 
v___x_1418_ = lean_st_ref_take(v_a_1407_);
v_rewriteSimpCache_1419_ = lean_ctor_get(v___x_1418_, 0);
v_rewriteDSimpCache_1420_ = lean_ctor_get(v___x_1418_, 1);
v_typeAnalysis_1421_ = lean_ctor_get(v___x_1418_, 3);
v_target_1422_ = lean_ctor_get(v___x_1418_, 4);
v_hypotheses_1423_ = lean_ctor_get(v___x_1418_, 5);
v_didChange_1424_ = lean_ctor_get_uint8(v___x_1418_, sizeof(void*)*6);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v___x_1418_, 2);
lean_dec(v_unused_1436_);
v___x_1426_ = v___x_1418_;
v_isShared_1427_ = v_isSharedCheck_1435_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_hypotheses_1423_);
lean_inc(v_target_1422_);
lean_inc(v_typeAnalysis_1421_);
lean_inc(v_rewriteDSimpCache_1420_);
lean_inc(v_rewriteSimpCache_1419_);
lean_dec(v___x_1418_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1435_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 2, v___x_1428_);
v___x_1430_ = v___x_1426_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_rewriteSimpCache_1419_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_rewriteDSimpCache_1420_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_typeAnalysis_1421_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v_target_1422_);
lean_ctor_set(v_reuseFailAlloc_1434_, 5, v_hypotheses_1423_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, sizeof(void*)*6, v_didChange_1424_);
v___x_1430_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_st_ref_set(v_a_1407_, v___x_1430_);
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___boxed(lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache(v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(lean_object* v_a_1450_){
_start:
{
lean_object* v___x_1452_; lean_object* v_rewriteDSimpCache_1453_; lean_object* v_acCache_1454_; lean_object* v_typeAnalysis_1455_; lean_object* v_target_1456_; lean_object* v_hypotheses_1457_; uint8_t v_didChange_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1501_; 
v___x_1452_ = lean_st_ref_take(v_a_1450_);
v_rewriteDSimpCache_1453_ = lean_ctor_get(v___x_1452_, 1);
v_acCache_1454_ = lean_ctor_get(v___x_1452_, 2);
v_typeAnalysis_1455_ = lean_ctor_get(v___x_1452_, 3);
v_target_1456_ = lean_ctor_get(v___x_1452_, 4);
v_hypotheses_1457_ = lean_ctor_get(v___x_1452_, 5);
v_didChange_1458_ = lean_ctor_get_uint8(v___x_1452_, sizeof(void*)*6);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v___x_1452_, 0);
lean_dec(v_unused_1502_);
v___x_1460_ = v___x_1452_;
v_isShared_1461_ = v_isSharedCheck_1501_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_hypotheses_1457_);
lean_inc(v_target_1456_);
lean_inc(v_typeAnalysis_1455_);
lean_inc(v_acCache_1454_);
lean_inc(v_rewriteDSimpCache_1453_);
lean_dec(v___x_1452_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1501_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1462_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_rewriteDSimpCache_1453_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_acCache_1454_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_typeAnalysis_1455_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_target_1456_);
lean_ctor_set(v_reuseFailAlloc_1500_, 5, v_hypotheses_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*6, v_didChange_1458_);
v___x_1464_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v_rewriteSimpCache_1467_; lean_object* v_acCache_1468_; lean_object* v_typeAnalysis_1469_; lean_object* v_target_1470_; lean_object* v_hypotheses_1471_; uint8_t v_didChange_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1498_; 
v___x_1465_ = lean_st_ref_set(v_a_1450_, v___x_1464_);
v___x_1466_ = lean_st_ref_take(v_a_1450_);
v_rewriteSimpCache_1467_ = lean_ctor_get(v___x_1466_, 0);
v_acCache_1468_ = lean_ctor_get(v___x_1466_, 2);
v_typeAnalysis_1469_ = lean_ctor_get(v___x_1466_, 3);
v_target_1470_ = lean_ctor_get(v___x_1466_, 4);
v_hypotheses_1471_ = lean_ctor_get(v___x_1466_, 5);
v_didChange_1472_ = lean_ctor_get_uint8(v___x_1466_, sizeof(void*)*6);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; 
v_unused_1499_ = lean_ctor_get(v___x_1466_, 1);
lean_dec(v_unused_1499_);
v___x_1474_ = v___x_1466_;
v_isShared_1475_ = v_isSharedCheck_1498_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_hypotheses_1471_);
lean_inc(v_target_1470_);
lean_inc(v_typeAnalysis_1469_);
lean_inc(v_acCache_1468_);
lean_inc(v_rewriteSimpCache_1467_);
lean_dec(v___x_1466_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1498_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v___x_1462_);
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_rewriteSimpCache_1467_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_acCache_1468_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v_typeAnalysis_1469_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v_target_1470_);
lean_ctor_set(v_reuseFailAlloc_1497_, 5, v_hypotheses_1471_);
lean_ctor_set_uint8(v_reuseFailAlloc_1497_, sizeof(void*)*6, v_didChange_1472_);
v___x_1477_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_rewriteSimpCache_1480_; lean_object* v_rewriteDSimpCache_1481_; lean_object* v_typeAnalysis_1482_; lean_object* v_target_1483_; lean_object* v_hypotheses_1484_; uint8_t v_didChange_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1495_; 
v___x_1478_ = lean_st_ref_set(v_a_1450_, v___x_1477_);
v___x_1479_ = lean_st_ref_take(v_a_1450_);
v_rewriteSimpCache_1480_ = lean_ctor_get(v___x_1479_, 0);
v_rewriteDSimpCache_1481_ = lean_ctor_get(v___x_1479_, 1);
v_typeAnalysis_1482_ = lean_ctor_get(v___x_1479_, 3);
v_target_1483_ = lean_ctor_get(v___x_1479_, 4);
v_hypotheses_1484_ = lean_ctor_get(v___x_1479_, 5);
v_didChange_1485_ = lean_ctor_get_uint8(v___x_1479_, sizeof(void*)*6);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; 
v_unused_1496_ = lean_ctor_get(v___x_1479_, 2);
lean_dec(v_unused_1496_);
v___x_1487_ = v___x_1479_;
v_isShared_1488_ = v_isSharedCheck_1495_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_hypotheses_1484_);
lean_inc(v_target_1483_);
lean_inc(v_typeAnalysis_1482_);
lean_inc(v_rewriteDSimpCache_1481_);
lean_inc(v_rewriteSimpCache_1480_);
lean_dec(v___x_1479_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1495_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 2, v___x_1462_);
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_rewriteSimpCache_1480_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_rewriteDSimpCache_1481_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1494_, 3, v_typeAnalysis_1482_);
lean_ctor_set(v_reuseFailAlloc_1494_, 4, v_target_1483_);
lean_ctor_set(v_reuseFailAlloc_1494_, 5, v_hypotheses_1484_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*6, v_didChange_1485_);
v___x_1490_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = lean_st_ref_set(v_a_1450_, v___x_1490_);
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
return v___x_1493_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg___boxed(lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(v_a_1503_);
lean_dec(v_a_1503_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches(lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(v_a_1507_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___boxed(lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches(v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
lean_dec(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object* v_a_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v_typeAnalysis_1535_; lean_object* v___x_1536_; 
v___x_1534_ = lean_st_ref_get(v_a_1532_);
v_typeAnalysis_1535_ = lean_ctor_get(v___x_1534_, 3);
lean_inc_ref(v_typeAnalysis_1535_);
lean_dec(v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v_typeAnalysis_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_1537_);
lean_dec(v_a_1537_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v_typeAnalysis_1553_; lean_object* v___x_1554_; 
v___x_1552_ = lean_st_ref_get(v_a_1541_);
v_typeAnalysis_1553_ = lean_ctor_get(v___x_1552_, 3);
lean_inc_ref(v_typeAnalysis_1553_);
lean_dec(v___x_1552_);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v_typeAnalysis_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object* v_n_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v___x_1576_; lean_object* v_typeAnalysis_1577_; lean_object* v_interestingStructures_1578_; lean_object* v_uninteresting_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1576_ = lean_st_ref_get(v_a_1574_);
v_typeAnalysis_1577_ = lean_ctor_get(v___x_1576_, 3);
lean_inc_ref(v_typeAnalysis_1577_);
lean_dec(v___x_1576_);
v_interestingStructures_1578_ = lean_ctor_get(v_typeAnalysis_1577_, 0);
lean_inc_ref(v_interestingStructures_1578_);
v_uninteresting_1579_ = lean_ctor_get(v_typeAnalysis_1577_, 3);
lean_inc_ref(v_uninteresting_1579_);
lean_dec_ref(v_typeAnalysis_1577_);
v___x_1580_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1581_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
lean_inc(v_n_1573_);
v___x_1582_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1580_, v___x_1581_, v_uninteresting_1579_, v_n_1573_);
lean_dec_ref(v_uninteresting_1579_);
if (v___x_1582_ == 0)
{
uint8_t v___x_1583_; 
v___x_1583_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1580_, v___x_1581_, v_interestingStructures_1578_, v_n_1573_);
lean_dec_ref(v_interestingStructures_1578_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_box(0);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = lean_box(v___x_1583_);
v___x_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec_ref(v_interestingStructures_1578_);
lean_dec(v_n_1573_);
v___x_1589_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object* v_n_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(v_n_1591_, v_a_1592_);
lean_dec(v_a_1592_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object* v_n_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v_typeAnalysis_1609_; lean_object* v_interestingStructures_1610_; lean_object* v_uninteresting_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1608_ = lean_st_ref_get(v_a_1597_);
v_typeAnalysis_1609_ = lean_ctor_get(v___x_1608_, 3);
lean_inc_ref(v_typeAnalysis_1609_);
lean_dec(v___x_1608_);
v_interestingStructures_1610_ = lean_ctor_get(v_typeAnalysis_1609_, 0);
lean_inc_ref(v_interestingStructures_1610_);
v_uninteresting_1611_ = lean_ctor_get(v_typeAnalysis_1609_, 3);
lean_inc_ref(v_uninteresting_1611_);
lean_dec_ref(v_typeAnalysis_1609_);
v___x_1612_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1613_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
lean_inc(v_n_1595_);
v___x_1614_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1612_, v___x_1613_, v_uninteresting_1611_, v_n_1595_);
lean_dec_ref(v_uninteresting_1611_);
if (v___x_1614_ == 0)
{
uint8_t v___x_1615_; 
v___x_1615_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1612_, v___x_1613_, v_interestingStructures_1610_, v_n_1595_);
lean_dec_ref(v_interestingStructures_1610_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_box(0);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = lean_box(v___x_1615_);
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
v___x_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
return v___x_1620_;
}
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v_interestingStructures_1610_);
lean_dec(v_n_1595_);
v___x_1621_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object* v_n_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(v_n_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object* v_f_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v_rewriteSimpCache_1641_; lean_object* v_rewriteDSimpCache_1642_; lean_object* v_acCache_1643_; lean_object* v_typeAnalysis_1644_; lean_object* v_target_1645_; lean_object* v_hypotheses_1646_; uint8_t v_didChange_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1658_; 
v___x_1640_ = lean_st_ref_take(v_a_1638_);
v_rewriteSimpCache_1641_ = lean_ctor_get(v___x_1640_, 0);
v_rewriteDSimpCache_1642_ = lean_ctor_get(v___x_1640_, 1);
v_acCache_1643_ = lean_ctor_get(v___x_1640_, 2);
v_typeAnalysis_1644_ = lean_ctor_get(v___x_1640_, 3);
v_target_1645_ = lean_ctor_get(v___x_1640_, 4);
v_hypotheses_1646_ = lean_ctor_get(v___x_1640_, 5);
v_didChange_1647_ = lean_ctor_get_uint8(v___x_1640_, sizeof(void*)*6);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1649_ = v___x_1640_;
v_isShared_1650_ = v_isSharedCheck_1658_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_hypotheses_1646_);
lean_inc(v_target_1645_);
lean_inc(v_typeAnalysis_1644_);
lean_inc(v_acCache_1643_);
lean_inc(v_rewriteDSimpCache_1642_);
lean_inc(v_rewriteSimpCache_1641_);
lean_dec(v___x_1640_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1658_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_apply_1(v_f_1637_, v_typeAnalysis_1644_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 3, v___x_1651_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_rewriteSimpCache_1641_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_rewriteDSimpCache_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_acCache_1643_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v_target_1645_);
lean_ctor_set(v_reuseFailAlloc_1657_, 5, v_hypotheses_1646_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*6, v_didChange_1647_);
v___x_1653_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_st_ref_set(v_a_1638_, v___x_1653_);
v___x_1655_ = lean_box(0);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object* v_f_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(v_f_1659_, v_a_1660_);
lean_dec(v_a_1660_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object* v_f_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v___x_1676_; lean_object* v_rewriteSimpCache_1677_; lean_object* v_rewriteDSimpCache_1678_; lean_object* v_acCache_1679_; lean_object* v_typeAnalysis_1680_; lean_object* v_target_1681_; lean_object* v_hypotheses_1682_; uint8_t v_didChange_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1694_; 
v___x_1676_ = lean_st_ref_take(v_a_1665_);
v_rewriteSimpCache_1677_ = lean_ctor_get(v___x_1676_, 0);
v_rewriteDSimpCache_1678_ = lean_ctor_get(v___x_1676_, 1);
v_acCache_1679_ = lean_ctor_get(v___x_1676_, 2);
v_typeAnalysis_1680_ = lean_ctor_get(v___x_1676_, 3);
v_target_1681_ = lean_ctor_get(v___x_1676_, 4);
v_hypotheses_1682_ = lean_ctor_get(v___x_1676_, 5);
v_didChange_1683_ = lean_ctor_get_uint8(v___x_1676_, sizeof(void*)*6);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1685_ = v___x_1676_;
v_isShared_1686_ = v_isSharedCheck_1694_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_hypotheses_1682_);
lean_inc(v_target_1681_);
lean_inc(v_typeAnalysis_1680_);
lean_inc(v_acCache_1679_);
lean_inc(v_rewriteDSimpCache_1678_);
lean_inc(v_rewriteSimpCache_1677_);
lean_dec(v___x_1676_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1694_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_apply_1(v_f_1663_, v_typeAnalysis_1680_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 3, v___x_1687_);
v___x_1689_ = v___x_1685_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_rewriteSimpCache_1677_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_rewriteDSimpCache_1678_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_acCache_1679_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_target_1681_);
lean_ctor_set(v_reuseFailAlloc_1693_, 5, v_hypotheses_1682_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*6, v_didChange_1683_);
v___x_1689_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = lean_st_ref_set(v_a_1665_, v___x_1689_);
v___x_1691_ = lean_box(0);
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
return v___x_1692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object* v_f_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(v_f_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object* v_n_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v___x_1712_; lean_object* v_typeAnalysis_1713_; lean_object* v_rewriteSimpCache_1714_; lean_object* v_rewriteDSimpCache_1715_; lean_object* v_acCache_1716_; lean_object* v_target_1717_; lean_object* v_hypotheses_1718_; uint8_t v_didChange_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1743_; 
v___x_1712_ = lean_st_ref_take(v_a_1710_);
v_typeAnalysis_1713_ = lean_ctor_get(v___x_1712_, 3);
v_rewriteSimpCache_1714_ = lean_ctor_get(v___x_1712_, 0);
v_rewriteDSimpCache_1715_ = lean_ctor_get(v___x_1712_, 1);
v_acCache_1716_ = lean_ctor_get(v___x_1712_, 2);
v_target_1717_ = lean_ctor_get(v___x_1712_, 4);
v_hypotheses_1718_ = lean_ctor_get(v___x_1712_, 5);
v_didChange_1719_ = lean_ctor_get_uint8(v___x_1712_, sizeof(void*)*6);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1721_ = v___x_1712_;
v_isShared_1722_ = v_isSharedCheck_1743_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_hypotheses_1718_);
lean_inc(v_target_1717_);
lean_inc(v_typeAnalysis_1713_);
lean_inc(v_acCache_1716_);
lean_inc(v_rewriteDSimpCache_1715_);
lean_inc(v_rewriteSimpCache_1714_);
lean_dec(v___x_1712_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1743_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_interestingStructures_1723_; lean_object* v_interestingEnums_1724_; lean_object* v_interestingMatchers_1725_; lean_object* v_uninteresting_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1742_; 
v_interestingStructures_1723_ = lean_ctor_get(v_typeAnalysis_1713_, 0);
v_interestingEnums_1724_ = lean_ctor_get(v_typeAnalysis_1713_, 1);
v_interestingMatchers_1725_ = lean_ctor_get(v_typeAnalysis_1713_, 2);
v_uninteresting_1726_ = lean_ctor_get(v_typeAnalysis_1713_, 3);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_typeAnalysis_1713_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1728_ = v_typeAnalysis_1713_;
v_isShared_1729_ = v_isSharedCheck_1742_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_uninteresting_1726_);
lean_inc(v_interestingMatchers_1725_);
lean_inc(v_interestingEnums_1724_);
lean_inc(v_interestingStructures_1723_);
lean_dec(v_typeAnalysis_1713_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1742_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1730_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1731_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1732_ = lean_box(0);
v___x_1733_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1730_, v___x_1731_, v_interestingStructures_1723_, v_n_1709_, v___x_1732_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1733_);
v___x_1735_ = v___x_1728_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_interestingEnums_1724_);
lean_ctor_set(v_reuseFailAlloc_1741_, 2, v_interestingMatchers_1725_);
lean_ctor_set(v_reuseFailAlloc_1741_, 3, v_uninteresting_1726_);
v___x_1735_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 3, v___x_1735_);
v___x_1737_ = v___x_1721_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_rewriteSimpCache_1714_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_rewriteDSimpCache_1715_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_acCache_1716_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_target_1717_);
lean_ctor_set(v_reuseFailAlloc_1740_, 5, v_hypotheses_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1740_, sizeof(void*)*6, v_didChange_1719_);
v___x_1737_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_st_ref_set(v_a_1710_, v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1732_);
return v___x_1739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object* v_n_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(v_n_1744_, v_a_1745_);
lean_dec(v_a_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object* v_n_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1761_; lean_object* v_typeAnalysis_1762_; lean_object* v_rewriteSimpCache_1763_; lean_object* v_rewriteDSimpCache_1764_; lean_object* v_acCache_1765_; lean_object* v_target_1766_; lean_object* v_hypotheses_1767_; uint8_t v_didChange_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1792_; 
v___x_1761_ = lean_st_ref_take(v_a_1750_);
v_typeAnalysis_1762_ = lean_ctor_get(v___x_1761_, 3);
v_rewriteSimpCache_1763_ = lean_ctor_get(v___x_1761_, 0);
v_rewriteDSimpCache_1764_ = lean_ctor_get(v___x_1761_, 1);
v_acCache_1765_ = lean_ctor_get(v___x_1761_, 2);
v_target_1766_ = lean_ctor_get(v___x_1761_, 4);
v_hypotheses_1767_ = lean_ctor_get(v___x_1761_, 5);
v_didChange_1768_ = lean_ctor_get_uint8(v___x_1761_, sizeof(void*)*6);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1770_ = v___x_1761_;
v_isShared_1771_ = v_isSharedCheck_1792_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_hypotheses_1767_);
lean_inc(v_target_1766_);
lean_inc(v_typeAnalysis_1762_);
lean_inc(v_acCache_1765_);
lean_inc(v_rewriteDSimpCache_1764_);
lean_inc(v_rewriteSimpCache_1763_);
lean_dec(v___x_1761_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1792_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_interestingStructures_1772_; lean_object* v_interestingEnums_1773_; lean_object* v_interestingMatchers_1774_; lean_object* v_uninteresting_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1791_; 
v_interestingStructures_1772_ = lean_ctor_get(v_typeAnalysis_1762_, 0);
v_interestingEnums_1773_ = lean_ctor_get(v_typeAnalysis_1762_, 1);
v_interestingMatchers_1774_ = lean_ctor_get(v_typeAnalysis_1762_, 2);
v_uninteresting_1775_ = lean_ctor_get(v_typeAnalysis_1762_, 3);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_typeAnalysis_1762_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1777_ = v_typeAnalysis_1762_;
v_isShared_1778_ = v_isSharedCheck_1791_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_uninteresting_1775_);
lean_inc(v_interestingMatchers_1774_);
lean_inc(v_interestingEnums_1773_);
lean_inc(v_interestingStructures_1772_);
lean_dec(v_typeAnalysis_1762_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1791_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1779_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1780_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1781_ = lean_box(0);
v___x_1782_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1779_, v___x_1780_, v_interestingStructures_1772_, v_n_1748_, v___x_1781_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1782_);
v___x_1784_ = v___x_1777_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_interestingEnums_1773_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_interestingMatchers_1774_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_uninteresting_1775_);
v___x_1784_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1786_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 3, v___x_1784_);
v___x_1786_ = v___x_1770_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_rewriteSimpCache_1763_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_rewriteDSimpCache_1764_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_acCache_1765_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v_target_1766_);
lean_ctor_set(v_reuseFailAlloc_1789_, 5, v_hypotheses_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*6, v_didChange_1768_);
v___x_1786_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_st_ref_set(v_a_1750_, v___x_1786_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1781_);
return v___x_1788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object* v_n_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(v_n_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object* v_n_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v___x_1810_; lean_object* v_typeAnalysis_1811_; lean_object* v_rewriteSimpCache_1812_; lean_object* v_rewriteDSimpCache_1813_; lean_object* v_acCache_1814_; lean_object* v_target_1815_; lean_object* v_hypotheses_1816_; uint8_t v_didChange_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1841_; 
v___x_1810_ = lean_st_ref_take(v_a_1808_);
v_typeAnalysis_1811_ = lean_ctor_get(v___x_1810_, 3);
v_rewriteSimpCache_1812_ = lean_ctor_get(v___x_1810_, 0);
v_rewriteDSimpCache_1813_ = lean_ctor_get(v___x_1810_, 1);
v_acCache_1814_ = lean_ctor_get(v___x_1810_, 2);
v_target_1815_ = lean_ctor_get(v___x_1810_, 4);
v_hypotheses_1816_ = lean_ctor_get(v___x_1810_, 5);
v_didChange_1817_ = lean_ctor_get_uint8(v___x_1810_, sizeof(void*)*6);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1819_ = v___x_1810_;
v_isShared_1820_ = v_isSharedCheck_1841_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_hypotheses_1816_);
lean_inc(v_target_1815_);
lean_inc(v_typeAnalysis_1811_);
lean_inc(v_acCache_1814_);
lean_inc(v_rewriteDSimpCache_1813_);
lean_inc(v_rewriteSimpCache_1812_);
lean_dec(v___x_1810_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1841_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_interestingStructures_1821_; lean_object* v_interestingEnums_1822_; lean_object* v_interestingMatchers_1823_; lean_object* v_uninteresting_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1840_; 
v_interestingStructures_1821_ = lean_ctor_get(v_typeAnalysis_1811_, 0);
v_interestingEnums_1822_ = lean_ctor_get(v_typeAnalysis_1811_, 1);
v_interestingMatchers_1823_ = lean_ctor_get(v_typeAnalysis_1811_, 2);
v_uninteresting_1824_ = lean_ctor_get(v_typeAnalysis_1811_, 3);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_typeAnalysis_1811_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1826_ = v_typeAnalysis_1811_;
v_isShared_1827_ = v_isSharedCheck_1840_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_uninteresting_1824_);
lean_inc(v_interestingMatchers_1823_);
lean_inc(v_interestingEnums_1822_);
lean_inc(v_interestingStructures_1821_);
lean_dec(v_typeAnalysis_1811_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1840_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1828_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1829_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1830_ = lean_box(0);
v___x_1831_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1828_, v___x_1829_, v_interestingEnums_1822_, v_n_1807_, v___x_1830_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___x_1831_);
v___x_1833_ = v___x_1826_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_interestingStructures_1821_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v_interestingMatchers_1823_);
lean_ctor_set(v_reuseFailAlloc_1839_, 3, v_uninteresting_1824_);
v___x_1833_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1835_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 3, v___x_1833_);
v___x_1835_ = v___x_1819_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_rewriteSimpCache_1812_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_rewriteDSimpCache_1813_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v_acCache_1814_);
lean_ctor_set(v_reuseFailAlloc_1838_, 3, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1838_, 4, v_target_1815_);
lean_ctor_set(v_reuseFailAlloc_1838_, 5, v_hypotheses_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, sizeof(void*)*6, v_didChange_1817_);
v___x_1835_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = lean_st_ref_set(v_a_1808_, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1830_);
return v___x_1837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object* v_n_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(v_n_1842_, v_a_1843_);
lean_dec(v_a_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object* v_n_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1859_; lean_object* v_typeAnalysis_1860_; lean_object* v_rewriteSimpCache_1861_; lean_object* v_rewriteDSimpCache_1862_; lean_object* v_acCache_1863_; lean_object* v_target_1864_; lean_object* v_hypotheses_1865_; uint8_t v_didChange_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1890_; 
v___x_1859_ = lean_st_ref_take(v_a_1848_);
v_typeAnalysis_1860_ = lean_ctor_get(v___x_1859_, 3);
v_rewriteSimpCache_1861_ = lean_ctor_get(v___x_1859_, 0);
v_rewriteDSimpCache_1862_ = lean_ctor_get(v___x_1859_, 1);
v_acCache_1863_ = lean_ctor_get(v___x_1859_, 2);
v_target_1864_ = lean_ctor_get(v___x_1859_, 4);
v_hypotheses_1865_ = lean_ctor_get(v___x_1859_, 5);
v_didChange_1866_ = lean_ctor_get_uint8(v___x_1859_, sizeof(void*)*6);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1868_ = v___x_1859_;
v_isShared_1869_ = v_isSharedCheck_1890_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_hypotheses_1865_);
lean_inc(v_target_1864_);
lean_inc(v_typeAnalysis_1860_);
lean_inc(v_acCache_1863_);
lean_inc(v_rewriteDSimpCache_1862_);
lean_inc(v_rewriteSimpCache_1861_);
lean_dec(v___x_1859_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1890_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v_interestingStructures_1870_; lean_object* v_interestingEnums_1871_; lean_object* v_interestingMatchers_1872_; lean_object* v_uninteresting_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1889_; 
v_interestingStructures_1870_ = lean_ctor_get(v_typeAnalysis_1860_, 0);
v_interestingEnums_1871_ = lean_ctor_get(v_typeAnalysis_1860_, 1);
v_interestingMatchers_1872_ = lean_ctor_get(v_typeAnalysis_1860_, 2);
v_uninteresting_1873_ = lean_ctor_get(v_typeAnalysis_1860_, 3);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_typeAnalysis_1860_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1875_ = v_typeAnalysis_1860_;
v_isShared_1876_ = v_isSharedCheck_1889_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_uninteresting_1873_);
lean_inc(v_interestingMatchers_1872_);
lean_inc(v_interestingEnums_1871_);
lean_inc(v_interestingStructures_1870_);
lean_dec(v_typeAnalysis_1860_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1889_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1877_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1878_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1879_ = lean_box(0);
v___x_1880_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1877_, v___x_1878_, v_interestingEnums_1871_, v_n_1846_, v___x_1879_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 1, v___x_1880_);
v___x_1882_ = v___x_1875_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_interestingStructures_1870_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_interestingMatchers_1872_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_uninteresting_1873_);
v___x_1882_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1884_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 3, v___x_1882_);
v___x_1884_ = v___x_1868_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_rewriteSimpCache_1861_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_rewriteDSimpCache_1862_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v_acCache_1863_);
lean_ctor_set(v_reuseFailAlloc_1887_, 3, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1887_, 4, v_target_1864_);
lean_ctor_set(v_reuseFailAlloc_1887_, 5, v_hypotheses_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*6, v_didChange_1866_);
v___x_1884_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_st_ref_set(v_a_1848_, v___x_1884_);
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1879_);
return v___x_1886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object* v_n_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(v_n_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object* v_n_1905_, lean_object* v_k_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v_typeAnalysis_1910_; lean_object* v_rewriteSimpCache_1911_; lean_object* v_rewriteDSimpCache_1912_; lean_object* v_acCache_1913_; lean_object* v_target_1914_; lean_object* v_hypotheses_1915_; uint8_t v_didChange_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1940_; 
v___x_1909_ = lean_st_ref_take(v_a_1907_);
v_typeAnalysis_1910_ = lean_ctor_get(v___x_1909_, 3);
v_rewriteSimpCache_1911_ = lean_ctor_get(v___x_1909_, 0);
v_rewriteDSimpCache_1912_ = lean_ctor_get(v___x_1909_, 1);
v_acCache_1913_ = lean_ctor_get(v___x_1909_, 2);
v_target_1914_ = lean_ctor_get(v___x_1909_, 4);
v_hypotheses_1915_ = lean_ctor_get(v___x_1909_, 5);
v_didChange_1916_ = lean_ctor_get_uint8(v___x_1909_, sizeof(void*)*6);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1918_ = v___x_1909_;
v_isShared_1919_ = v_isSharedCheck_1940_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_hypotheses_1915_);
lean_inc(v_target_1914_);
lean_inc(v_typeAnalysis_1910_);
lean_inc(v_acCache_1913_);
lean_inc(v_rewriteDSimpCache_1912_);
lean_inc(v_rewriteSimpCache_1911_);
lean_dec(v___x_1909_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1940_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_interestingStructures_1920_; lean_object* v_interestingEnums_1921_; lean_object* v_interestingMatchers_1922_; lean_object* v_uninteresting_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1939_; 
v_interestingStructures_1920_ = lean_ctor_get(v_typeAnalysis_1910_, 0);
v_interestingEnums_1921_ = lean_ctor_get(v_typeAnalysis_1910_, 1);
v_interestingMatchers_1922_ = lean_ctor_get(v_typeAnalysis_1910_, 2);
v_uninteresting_1923_ = lean_ctor_get(v_typeAnalysis_1910_, 3);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_typeAnalysis_1910_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1925_ = v_typeAnalysis_1910_;
v_isShared_1926_ = v_isSharedCheck_1939_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_uninteresting_1923_);
lean_inc(v_interestingMatchers_1922_);
lean_inc(v_interestingEnums_1921_);
lean_inc(v_interestingStructures_1920_);
lean_dec(v_typeAnalysis_1910_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1939_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1927_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1928_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1929_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1927_, v___x_1928_, v_interestingMatchers_1922_, v_n_1905_, v_k_1906_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 2, v___x_1929_);
v___x_1931_ = v___x_1925_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_interestingStructures_1920_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_interestingEnums_1921_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_uninteresting_1923_);
v___x_1931_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1933_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 3, v___x_1931_);
v___x_1933_ = v___x_1918_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_rewriteSimpCache_1911_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_rewriteDSimpCache_1912_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_acCache_1913_);
lean_ctor_set(v_reuseFailAlloc_1937_, 3, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1937_, 4, v_target_1914_);
lean_ctor_set(v_reuseFailAlloc_1937_, 5, v_hypotheses_1915_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*6, v_didChange_1916_);
v___x_1933_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = lean_st_ref_set(v_a_1907_, v___x_1933_);
v___x_1935_ = lean_box(0);
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
return v___x_1936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object* v_n_1941_, lean_object* v_k_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(v_n_1941_, v_k_1942_, v_a_1943_);
lean_dec(v_a_1943_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object* v_n_1946_, lean_object* v_k_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v___x_1960_; lean_object* v_typeAnalysis_1961_; lean_object* v_rewriteSimpCache_1962_; lean_object* v_rewriteDSimpCache_1963_; lean_object* v_acCache_1964_; lean_object* v_target_1965_; lean_object* v_hypotheses_1966_; uint8_t v_didChange_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1991_; 
v___x_1960_ = lean_st_ref_take(v_a_1949_);
v_typeAnalysis_1961_ = lean_ctor_get(v___x_1960_, 3);
v_rewriteSimpCache_1962_ = lean_ctor_get(v___x_1960_, 0);
v_rewriteDSimpCache_1963_ = lean_ctor_get(v___x_1960_, 1);
v_acCache_1964_ = lean_ctor_get(v___x_1960_, 2);
v_target_1965_ = lean_ctor_get(v___x_1960_, 4);
v_hypotheses_1966_ = lean_ctor_get(v___x_1960_, 5);
v_didChange_1967_ = lean_ctor_get_uint8(v___x_1960_, sizeof(void*)*6);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1969_ = v___x_1960_;
v_isShared_1970_ = v_isSharedCheck_1991_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_hypotheses_1966_);
lean_inc(v_target_1965_);
lean_inc(v_typeAnalysis_1961_);
lean_inc(v_acCache_1964_);
lean_inc(v_rewriteDSimpCache_1963_);
lean_inc(v_rewriteSimpCache_1962_);
lean_dec(v___x_1960_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1991_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v_interestingStructures_1971_; lean_object* v_interestingEnums_1972_; lean_object* v_interestingMatchers_1973_; lean_object* v_uninteresting_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1990_; 
v_interestingStructures_1971_ = lean_ctor_get(v_typeAnalysis_1961_, 0);
v_interestingEnums_1972_ = lean_ctor_get(v_typeAnalysis_1961_, 1);
v_interestingMatchers_1973_ = lean_ctor_get(v_typeAnalysis_1961_, 2);
v_uninteresting_1974_ = lean_ctor_get(v_typeAnalysis_1961_, 3);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_typeAnalysis_1961_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1976_ = v_typeAnalysis_1961_;
v_isShared_1977_ = v_isSharedCheck_1990_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_uninteresting_1974_);
lean_inc(v_interestingMatchers_1973_);
lean_inc(v_interestingEnums_1972_);
lean_inc(v_interestingStructures_1971_);
lean_dec(v_typeAnalysis_1961_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1990_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1978_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1979_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1980_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1978_, v___x_1979_, v_interestingMatchers_1973_, v_n_1946_, v_k_1947_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 2, v___x_1980_);
v___x_1982_ = v___x_1976_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_interestingStructures_1971_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_interestingEnums_1972_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v_uninteresting_1974_);
v___x_1982_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1984_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 3, v___x_1982_);
v___x_1984_ = v___x_1969_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_rewriteSimpCache_1962_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_rewriteDSimpCache_1963_);
lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_acCache_1964_);
lean_ctor_set(v_reuseFailAlloc_1988_, 3, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1988_, 4, v_target_1965_);
lean_ctor_set(v_reuseFailAlloc_1988_, 5, v_hypotheses_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1988_, sizeof(void*)*6, v_didChange_1967_);
v___x_1984_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = lean_st_ref_set(v_a_1949_, v___x_1984_);
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
return v___x_1987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object* v_n_1992_, lean_object* v_k_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(v_n_1992_, v_k_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object* v_n_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___x_2010_; lean_object* v_typeAnalysis_2011_; lean_object* v_rewriteSimpCache_2012_; lean_object* v_rewriteDSimpCache_2013_; lean_object* v_acCache_2014_; lean_object* v_target_2015_; lean_object* v_hypotheses_2016_; uint8_t v_didChange_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2041_; 
v___x_2010_ = lean_st_ref_take(v_a_2008_);
v_typeAnalysis_2011_ = lean_ctor_get(v___x_2010_, 3);
v_rewriteSimpCache_2012_ = lean_ctor_get(v___x_2010_, 0);
v_rewriteDSimpCache_2013_ = lean_ctor_get(v___x_2010_, 1);
v_acCache_2014_ = lean_ctor_get(v___x_2010_, 2);
v_target_2015_ = lean_ctor_get(v___x_2010_, 4);
v_hypotheses_2016_ = lean_ctor_get(v___x_2010_, 5);
v_didChange_2017_ = lean_ctor_get_uint8(v___x_2010_, sizeof(void*)*6);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2019_ = v___x_2010_;
v_isShared_2020_ = v_isSharedCheck_2041_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_hypotheses_2016_);
lean_inc(v_target_2015_);
lean_inc(v_typeAnalysis_2011_);
lean_inc(v_acCache_2014_);
lean_inc(v_rewriteDSimpCache_2013_);
lean_inc(v_rewriteSimpCache_2012_);
lean_dec(v___x_2010_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2041_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v_interestingStructures_2021_; lean_object* v_interestingEnums_2022_; lean_object* v_interestingMatchers_2023_; lean_object* v_uninteresting_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2040_; 
v_interestingStructures_2021_ = lean_ctor_get(v_typeAnalysis_2011_, 0);
v_interestingEnums_2022_ = lean_ctor_get(v_typeAnalysis_2011_, 1);
v_interestingMatchers_2023_ = lean_ctor_get(v_typeAnalysis_2011_, 2);
v_uninteresting_2024_ = lean_ctor_get(v_typeAnalysis_2011_, 3);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_typeAnalysis_2011_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2026_ = v_typeAnalysis_2011_;
v_isShared_2027_ = v_isSharedCheck_2040_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_uninteresting_2024_);
lean_inc(v_interestingMatchers_2023_);
lean_inc(v_interestingEnums_2022_);
lean_inc(v_interestingStructures_2021_);
lean_dec(v_typeAnalysis_2011_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2040_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2028_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2029_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2030_ = lean_box(0);
v___x_2031_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2028_, v___x_2029_, v_uninteresting_2024_, v_n_2007_, v___x_2030_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 3, v___x_2031_);
v___x_2033_ = v___x_2026_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_interestingStructures_2021_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_interestingEnums_2022_);
lean_ctor_set(v_reuseFailAlloc_2039_, 2, v_interestingMatchers_2023_);
lean_ctor_set(v_reuseFailAlloc_2039_, 3, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2035_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 3, v___x_2033_);
v___x_2035_ = v___x_2019_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_rewriteSimpCache_2012_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_rewriteDSimpCache_2013_);
lean_ctor_set(v_reuseFailAlloc_2038_, 2, v_acCache_2014_);
lean_ctor_set(v_reuseFailAlloc_2038_, 3, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2038_, 4, v_target_2015_);
lean_ctor_set(v_reuseFailAlloc_2038_, 5, v_hypotheses_2016_);
lean_ctor_set_uint8(v_reuseFailAlloc_2038_, sizeof(void*)*6, v_didChange_2017_);
v___x_2035_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = lean_st_ref_set(v_a_2008_, v___x_2035_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2030_);
return v___x_2037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object* v_n_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(v_n_2042_, v_a_2043_);
lean_dec(v_a_2043_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object* v_n_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___x_2059_; lean_object* v_typeAnalysis_2060_; lean_object* v_rewriteSimpCache_2061_; lean_object* v_rewriteDSimpCache_2062_; lean_object* v_acCache_2063_; lean_object* v_target_2064_; lean_object* v_hypotheses_2065_; uint8_t v_didChange_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2090_; 
v___x_2059_ = lean_st_ref_take(v_a_2048_);
v_typeAnalysis_2060_ = lean_ctor_get(v___x_2059_, 3);
v_rewriteSimpCache_2061_ = lean_ctor_get(v___x_2059_, 0);
v_rewriteDSimpCache_2062_ = lean_ctor_get(v___x_2059_, 1);
v_acCache_2063_ = lean_ctor_get(v___x_2059_, 2);
v_target_2064_ = lean_ctor_get(v___x_2059_, 4);
v_hypotheses_2065_ = lean_ctor_get(v___x_2059_, 5);
v_didChange_2066_ = lean_ctor_get_uint8(v___x_2059_, sizeof(void*)*6);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2068_ = v___x_2059_;
v_isShared_2069_ = v_isSharedCheck_2090_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_hypotheses_2065_);
lean_inc(v_target_2064_);
lean_inc(v_typeAnalysis_2060_);
lean_inc(v_acCache_2063_);
lean_inc(v_rewriteDSimpCache_2062_);
lean_inc(v_rewriteSimpCache_2061_);
lean_dec(v___x_2059_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2090_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v_interestingStructures_2070_; lean_object* v_interestingEnums_2071_; lean_object* v_interestingMatchers_2072_; lean_object* v_uninteresting_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2089_; 
v_interestingStructures_2070_ = lean_ctor_get(v_typeAnalysis_2060_, 0);
v_interestingEnums_2071_ = lean_ctor_get(v_typeAnalysis_2060_, 1);
v_interestingMatchers_2072_ = lean_ctor_get(v_typeAnalysis_2060_, 2);
v_uninteresting_2073_ = lean_ctor_get(v_typeAnalysis_2060_, 3);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_typeAnalysis_2060_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2075_ = v_typeAnalysis_2060_;
v_isShared_2076_ = v_isSharedCheck_2089_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_uninteresting_2073_);
lean_inc(v_interestingMatchers_2072_);
lean_inc(v_interestingEnums_2071_);
lean_inc(v_interestingStructures_2070_);
lean_dec(v_typeAnalysis_2060_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2089_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2077_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_2078_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_2079_ = lean_box(0);
v___x_2080_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_2077_, v___x_2078_, v_uninteresting_2073_, v_n_2046_, v___x_2079_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 3, v___x_2080_);
v___x_2082_ = v___x_2075_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_interestingStructures_2070_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_interestingEnums_2071_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_interestingMatchers_2072_);
lean_ctor_set(v_reuseFailAlloc_2088_, 3, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2084_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 3, v___x_2082_);
v___x_2084_ = v___x_2068_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_rewriteSimpCache_2061_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_rewriteDSimpCache_2062_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_acCache_2063_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v_target_2064_);
lean_ctor_set(v_reuseFailAlloc_2087_, 5, v_hypotheses_2065_);
lean_ctor_set_uint8(v_reuseFailAlloc_2087_, sizeof(void*)*6, v_didChange_2066_);
v___x_2084_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_st_ref_set(v_a_2048_, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2079_);
return v___x_2086_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object* v_n_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(v_n_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2104_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_unsigned_to_nat(16u);
v___x_2107_ = lean_mk_array(v___x_2106_, v___x_2105_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0);
v___x_2109_ = lean_unsigned_to_nat(0u);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v___x_2108_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
v___x_2112_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
lean_ctor_set(v___x_2112_, 2, v___x_2111_);
lean_ctor_set(v___x_2112_, 3, v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object* v_ctx_2115_, lean_object* v_target_2116_, lean_object* v_x_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2128_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_2129_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2130_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2131_ = 0;
v___x_2132_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2132_, 0, v___x_2128_);
lean_ctor_set(v___x_2132_, 1, v___x_2128_);
lean_ctor_set(v___x_2132_, 2, v___x_2128_);
lean_ctor_set(v___x_2132_, 3, v___x_2129_);
lean_ctor_set(v___x_2132_, 4, v_target_2116_);
lean_ctor_set(v___x_2132_, 5, v___x_2130_);
lean_ctor_set_uint8(v___x_2132_, sizeof(void*)*6, v___x_2131_);
v___x_2133_ = lean_st_mk_ref(v___x_2132_);
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
lean_inc(v_a_2124_);
lean_inc_ref(v_a_2123_);
lean_inc(v_a_2122_);
lean_inc_ref(v_a_2121_);
lean_inc(v_a_2120_);
lean_inc_ref(v_a_2119_);
lean_inc(v_a_2118_);
lean_inc(v___x_2133_);
v___x_2134_ = lean_apply_12(v_x_2117_, v_ctx_2115_, v___x_2133_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, lean_box(0));
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2144_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2144_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2144_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2139_ = lean_st_ref_get(v___x_2133_);
lean_dec(v___x_2133_);
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v_a_2135_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2140_);
v___x_2142_ = v___x_2137_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v___x_2133_);
v_a_2145_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2134_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2134_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object* v_ctx_2153_, lean_object* v_target_2154_, lean_object* v_x_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(v_ctx_2153_, v_target_2154_, v_x_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object* v_00_u03b1_2167_, lean_object* v_ctx_2168_, lean_object* v_target_2169_, lean_object* v_x_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2181_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_2182_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2183_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2184_ = 0;
v___x_2185_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2185_, 0, v___x_2181_);
lean_ctor_set(v___x_2185_, 1, v___x_2181_);
lean_ctor_set(v___x_2185_, 2, v___x_2181_);
lean_ctor_set(v___x_2185_, 3, v___x_2182_);
lean_ctor_set(v___x_2185_, 4, v_target_2169_);
lean_ctor_set(v___x_2185_, 5, v___x_2183_);
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*6, v___x_2184_);
v___x_2186_ = lean_st_mk_ref(v___x_2185_);
lean_inc(v_a_2179_);
lean_inc_ref(v_a_2178_);
lean_inc(v_a_2177_);
lean_inc_ref(v_a_2176_);
lean_inc(v_a_2175_);
lean_inc_ref(v_a_2174_);
lean_inc(v_a_2173_);
lean_inc_ref(v_a_2172_);
lean_inc(v_a_2171_);
lean_inc(v___x_2186_);
v___x_2187_ = lean_apply_12(v_x_2170_, v_ctx_2168_, v___x_2186_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, lean_box(0));
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2197_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2190_ = v___x_2187_;
v_isShared_2191_ = v_isSharedCheck_2197_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2197_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2192_ = lean_st_ref_get(v___x_2186_);
lean_dec(v___x_2186_);
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v_a_2188_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2193_);
v___x_2195_ = v___x_2190_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v___x_2186_);
v_a_2198_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2187_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2187_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object* v_00_u03b1_2206_, lean_object* v_ctx_2207_, lean_object* v_target_2208_, lean_object* v_x_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(v_00_u03b1_2206_, v_ctx_2207_, v_target_2208_, v_x_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object* v_ctx_2221_, lean_object* v_target_2222_, lean_object* v_x_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2234_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_2235_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2236_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2237_ = 0;
v___x_2238_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2238_, 0, v___x_2234_);
lean_ctor_set(v___x_2238_, 1, v___x_2234_);
lean_ctor_set(v___x_2238_, 2, v___x_2234_);
lean_ctor_set(v___x_2238_, 3, v___x_2235_);
lean_ctor_set(v___x_2238_, 4, v_target_2222_);
lean_ctor_set(v___x_2238_, 5, v___x_2236_);
lean_ctor_set_uint8(v___x_2238_, sizeof(void*)*6, v___x_2237_);
v___x_2239_ = lean_st_mk_ref(v___x_2238_);
lean_inc(v_a_2232_);
lean_inc_ref(v_a_2231_);
lean_inc(v_a_2230_);
lean_inc_ref(v_a_2229_);
lean_inc(v_a_2228_);
lean_inc_ref(v_a_2227_);
lean_inc(v_a_2226_);
lean_inc_ref(v_a_2225_);
lean_inc(v_a_2224_);
lean_inc(v___x_2239_);
v___x_2240_ = lean_apply_12(v_x_2223_, v_ctx_2221_, v___x_2239_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, lean_box(0));
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2249_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = lean_st_ref_get(v___x_2239_);
lean_dec(v___x_2239_);
lean_dec(v___x_2245_);
if (v_isShared_2244_ == 0)
{
v___x_2247_ = v___x_2243_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2241_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_dec(v___x_2239_);
return v___x_2240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object* v_ctx_2250_, lean_object* v_target_2251_, lean_object* v_x_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(v_ctx_2250_, v_target_2251_, v_x_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec(v_a_2261_);
lean_dec_ref(v_a_2260_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object* v_00_u03b1_2264_, lean_object* v_ctx_2265_, lean_object* v_target_2266_, lean_object* v_x_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2278_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_2279_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_2280_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_2281_ = 0;
v___x_2282_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_2282_, 0, v___x_2278_);
lean_ctor_set(v___x_2282_, 1, v___x_2278_);
lean_ctor_set(v___x_2282_, 2, v___x_2278_);
lean_ctor_set(v___x_2282_, 3, v___x_2279_);
lean_ctor_set(v___x_2282_, 4, v_target_2266_);
lean_ctor_set(v___x_2282_, 5, v___x_2280_);
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*6, v___x_2281_);
v___x_2283_ = lean_st_mk_ref(v___x_2282_);
lean_inc(v_a_2276_);
lean_inc_ref(v_a_2275_);
lean_inc(v_a_2274_);
lean_inc_ref(v_a_2273_);
lean_inc(v_a_2272_);
lean_inc_ref(v_a_2271_);
lean_inc(v_a_2270_);
lean_inc_ref(v_a_2269_);
lean_inc(v_a_2268_);
lean_inc(v___x_2283_);
v___x_2284_ = lean_apply_12(v_x_2267_, v_ctx_2265_, v___x_2283_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, lean_box(0));
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2293_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2293_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2293_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v___x_2291_; 
v___x_2289_ = lean_st_ref_get(v___x_2283_);
lean_dec(v___x_2283_);
lean_dec(v___x_2289_);
if (v_isShared_2288_ == 0)
{
v___x_2291_ = v___x_2287_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2285_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
else
{
lean_dec(v___x_2283_);
return v___x_2284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object* v_00_u03b1_2294_, lean_object* v_ctx_2295_, lean_object* v_target_2296_, lean_object* v_x_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(v_00_u03b1_2294_, v_ctx_2295_, v_target_2296_, v_x_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
lean_dec(v_a_2304_);
lean_dec_ref(v_a_2303_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
return v_res_2308_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0(void){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_instMonadEIO(lean_box(0));
return v___x_2309_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0);
v___x_2311_ = l_StateRefT_x27_instMonad___redArg(v___x_2310_);
return v___x_2311_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2318_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2319_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2320_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2319_, v___x_2318_);
return v___x_2320_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___f_2322_; lean_object* v___x_2323_; 
v___x_2321_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8);
v___f_2322_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2323_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2322_, v___x_2321_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9);
v___x_2325_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2326_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2325_, v___x_2324_);
return v___x_2326_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___f_2328_; lean_object* v___x_2329_; 
v___x_2327_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___f_2328_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2329_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2328_, v___x_2327_);
return v___x_2329_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11);
v___x_2331_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2332_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2331_, v___x_2330_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; 
v___x_2333_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12);
v___f_2334_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2335_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2334_, v___x_2333_);
return v___x_2335_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___f_2337_; lean_object* v___x_2338_; 
v___x_2336_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13);
v___f_2337_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2338_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2337_, v___x_2336_);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2339_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14);
v___x_2340_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2341_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2340_, v___x_2339_);
return v___x_2341_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; 
v___x_2342_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15);
v___f_2343_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2344_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2343_, v___x_2342_);
return v___x_2344_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23(void){
_start:
{
lean_object* v_cls_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v_cls_2355_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
v___x_2356_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22));
v___x_2357_ = l_Lean_Name_append(v___x_2356_, v_cls_2355_);
return v___x_2357_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2360_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2361_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2362_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2363_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2362_, v___x_2361_, v___x_2360_);
return v___x_2363_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___f_2365_; lean_object* v___f_2366_; lean_object* v___x_2367_; 
v___x_2364_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26);
v___f_2365_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2366_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24));
v___x_2367_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2366_, v___f_2365_, v___x_2364_);
return v___x_2367_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2368_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27);
v___x_2369_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2370_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2371_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2370_, v___x_2369_, v___x_2368_);
return v___x_2371_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___f_2373_; lean_object* v___f_2374_; lean_object* v___x_2375_; 
v___x_2372_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v___f_2373_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2374_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24));
v___x_2375_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2374_, v___f_2373_, v___x_2372_);
return v___x_2375_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2376_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29);
v___x_2377_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2378_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2379_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2378_, v___x_2377_, v___x_2376_);
return v___x_2379_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___f_2381_; lean_object* v___f_2382_; lean_object* v___x_2383_; 
v___x_2380_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30);
v___f_2381_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2382_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24));
v___x_2383_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2382_, v___f_2381_, v___x_2380_);
return v___x_2383_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___f_2385_; lean_object* v___f_2386_; lean_object* v___x_2387_; 
v___x_2384_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31);
v___f_2385_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2386_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24));
v___x_2387_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2386_, v___f_2385_, v___x_2384_);
return v___x_2387_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2388_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32);
v___x_2389_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2390_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2391_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2390_, v___x_2389_, v___x_2388_);
return v___x_2391_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___f_2393_; lean_object* v___f_2394_; lean_object* v___x_2395_; 
v___x_2392_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33);
v___f_2393_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2394_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24));
v___x_2395_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2394_, v___f_2393_, v___x_2392_);
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___f_2398_; 
v___x_2396_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2397_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2398_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2398_, 0, v___x_2397_);
lean_closure_set(v___f_2398_, 1, v___x_2396_);
return v___f_2398_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36(void){
_start:
{
lean_object* v___f_2399_; lean_object* v___f_2400_; lean_object* v___f_2401_; 
v___f_2399_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2400_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__35);
v___f_2401_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2401_, 0, v___f_2400_);
lean_closure_set(v___f_2401_, 1, v___f_2399_);
return v___f_2401_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___f_2403_; lean_object* v___f_2404_; 
v___x_2402_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___f_2403_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__36);
v___f_2404_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2404_, 0, v___f_2403_);
lean_closure_set(v___f_2404_, 1, v___x_2402_);
return v___f_2404_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__38(void){
_start:
{
lean_object* v___f_2405_; lean_object* v___f_2406_; lean_object* v___f_2407_; 
v___f_2405_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2406_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__37);
v___f_2407_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2407_, 0, v___f_2406_);
lean_closure_set(v___f_2407_, 1, v___f_2405_);
return v___f_2407_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__39(void){
_start:
{
lean_object* v___f_2408_; lean_object* v___f_2409_; lean_object* v___f_2410_; 
v___f_2408_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2409_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__38, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__38_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__38);
v___f_2410_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2410_, 0, v___f_2409_);
lean_closure_set(v___f_2410_, 1, v___f_2408_);
return v___f_2410_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__40(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___f_2412_; lean_object* v___f_2413_; 
v___x_2411_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___f_2412_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__39, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__39_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__39);
v___f_2413_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2413_, 0, v___f_2412_);
lean_closure_set(v___f_2413_, 1, v___x_2411_);
return v___f_2413_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__41(void){
_start:
{
lean_object* v___f_2414_; lean_object* v___f_2415_; lean_object* v___f_2416_; 
v___f_2414_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2415_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__40, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__40_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__40);
v___f_2416_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2416_, 0, v___f_2415_);
lean_closure_set(v___f_2416_, 1, v___f_2414_);
return v___f_2416_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__43(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__42));
v___x_2419_ = l_Lean_stringToMessageData(v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object* v_hyp_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v___y_2434_; lean_object* v___x_2454_; lean_object* v_toApplicative_2455_; lean_object* v_toFunctor_2456_; lean_object* v_toSeq_2457_; lean_object* v_toSeqLeft_2458_; lean_object* v_toSeqRight_2459_; lean_object* v___f_2460_; lean_object* v___f_2461_; lean_object* v___f_2462_; lean_object* v___f_2463_; lean_object* v___x_2464_; lean_object* v___f_2465_; lean_object* v___f_2466_; lean_object* v___f_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v_toApplicative_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2521_; 
v___x_2454_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1);
v_toApplicative_2455_ = lean_ctor_get(v___x_2454_, 0);
v_toFunctor_2456_ = lean_ctor_get(v_toApplicative_2455_, 0);
v_toSeq_2457_ = lean_ctor_get(v_toApplicative_2455_, 2);
v_toSeqLeft_2458_ = lean_ctor_get(v_toApplicative_2455_, 3);
v_toSeqRight_2459_ = lean_ctor_get(v_toApplicative_2455_, 4);
v___f_2460_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2));
v___f_2461_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3));
lean_inc_ref_n(v_toFunctor_2456_, 2);
v___f_2462_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2462_, 0, v_toFunctor_2456_);
v___f_2463_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2463_, 0, v_toFunctor_2456_);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___f_2462_);
lean_ctor_set(v___x_2464_, 1, v___f_2463_);
lean_inc(v_toSeqRight_2459_);
v___f_2465_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2465_, 0, v_toSeqRight_2459_);
lean_inc(v_toSeqLeft_2458_);
v___f_2466_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2466_, 0, v_toSeqLeft_2458_);
lean_inc(v_toSeq_2457_);
v___f_2467_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2467_, 0, v_toSeq_2457_);
v___x_2468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2464_);
lean_ctor_set(v___x_2468_, 1, v___f_2460_);
lean_ctor_set(v___x_2468_, 2, v___f_2467_);
lean_ctor_set(v___x_2468_, 3, v___f_2466_);
lean_ctor_set(v___x_2468_, 4, v___f_2465_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
lean_ctor_set(v___x_2469_, 1, v___f_2461_);
v___x_2470_ = l_StateRefT_x27_instMonad___redArg(v___x_2469_);
v_toApplicative_2471_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2521_ == 0)
{
lean_object* v_unused_2522_; 
v_unused_2522_ = lean_ctor_get(v___x_2470_, 1);
lean_dec(v_unused_2522_);
v___x_2473_ = v___x_2470_;
v_isShared_2474_ = v_isSharedCheck_2521_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_toApplicative_2471_);
lean_dec(v___x_2470_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2521_;
goto v_resetjp_2472_;
}
v___jp_2433_:
{
lean_object* v___x_2435_; lean_object* v_rewriteSimpCache_2436_; lean_object* v_rewriteDSimpCache_2437_; lean_object* v_acCache_2438_; lean_object* v_typeAnalysis_2439_; lean_object* v_target_2440_; lean_object* v_hypotheses_2441_; uint8_t v_didChange_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2453_; 
v___x_2435_ = lean_st_ref_take(v___y_2434_);
v_rewriteSimpCache_2436_ = lean_ctor_get(v___x_2435_, 0);
v_rewriteDSimpCache_2437_ = lean_ctor_get(v___x_2435_, 1);
v_acCache_2438_ = lean_ctor_get(v___x_2435_, 2);
v_typeAnalysis_2439_ = lean_ctor_get(v___x_2435_, 3);
v_target_2440_ = lean_ctor_get(v___x_2435_, 4);
v_hypotheses_2441_ = lean_ctor_get(v___x_2435_, 5);
v_didChange_2442_ = lean_ctor_get_uint8(v___x_2435_, sizeof(void*)*6);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2444_ = v___x_2435_;
v_isShared_2445_ = v_isSharedCheck_2453_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_hypotheses_2441_);
lean_inc(v_target_2440_);
lean_inc(v_typeAnalysis_2439_);
lean_inc(v_acCache_2438_);
lean_inc(v_rewriteDSimpCache_2437_);
lean_inc(v_rewriteSimpCache_2436_);
lean_dec(v___x_2435_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2453_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = lean_array_push(v_hypotheses_2441_, v_hyp_2420_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 5, v___x_2446_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_rewriteSimpCache_2436_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_rewriteDSimpCache_2437_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_acCache_2438_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_typeAnalysis_2439_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_target_2440_);
lean_ctor_set(v_reuseFailAlloc_2452_, 5, v___x_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2452_, sizeof(void*)*6, v_didChange_2442_);
v___x_2448_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = lean_st_ref_set(v___y_2434_, v___x_2448_);
v___x_2450_ = lean_box(0);
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
return v___x_2451_;
}
}
}
v_resetjp_2472_:
{
lean_object* v_toFunctor_2475_; lean_object* v_toSeq_2476_; lean_object* v_toSeqLeft_2477_; lean_object* v_toSeqRight_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2519_; 
v_toFunctor_2475_ = lean_ctor_get(v_toApplicative_2471_, 0);
v_toSeq_2476_ = lean_ctor_get(v_toApplicative_2471_, 2);
v_toSeqLeft_2477_ = lean_ctor_get(v_toApplicative_2471_, 3);
v_toSeqRight_2478_ = lean_ctor_get(v_toApplicative_2471_, 4);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_toApplicative_2471_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; 
v_unused_2520_ = lean_ctor_get(v_toApplicative_2471_, 1);
lean_dec(v_unused_2520_);
v___x_2480_ = v_toApplicative_2471_;
v_isShared_2481_ = v_isSharedCheck_2519_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_toSeqRight_2478_);
lean_inc(v_toSeqLeft_2477_);
lean_inc(v_toSeq_2476_);
lean_inc(v_toFunctor_2475_);
lean_dec(v_toApplicative_2471_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2519_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___f_2482_; lean_object* v___f_2483_; lean_object* v___f_2484_; lean_object* v___f_2485_; lean_object* v___x_2486_; lean_object* v___f_2487_; lean_object* v___f_2488_; lean_object* v___f_2489_; lean_object* v___x_2491_; 
v___f_2482_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4));
v___f_2483_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5));
lean_inc_ref(v_toFunctor_2475_);
v___f_2484_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2484_, 0, v_toFunctor_2475_);
v___f_2485_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2485_, 0, v_toFunctor_2475_);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___f_2484_);
lean_ctor_set(v___x_2486_, 1, v___f_2485_);
v___f_2487_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2487_, 0, v_toSeqRight_2478_);
v___f_2488_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2488_, 0, v_toSeqLeft_2477_);
v___f_2489_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2489_, 0, v_toSeq_2476_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 4, v___f_2487_);
lean_ctor_set(v___x_2480_, 3, v___f_2488_);
lean_ctor_set(v___x_2480_, 2, v___f_2489_);
lean_ctor_set(v___x_2480_, 1, v___f_2482_);
lean_ctor_set(v___x_2480_, 0, v___x_2486_);
v___x_2491_ = v___x_2480_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v___f_2482_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v___f_2489_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v___f_2488_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v___f_2487_);
v___x_2491_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2493_; 
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 1, v___f_2483_);
lean_ctor_set(v___x_2473_, 0, v___x_2491_);
v___x_2493_ = v___x_2473_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v___f_2483_);
v___x_2493_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v_options_2502_; uint8_t v_hasTrace_2503_; 
v___x_2494_ = l_StateRefT_x27_instMonad___redArg(v___x_2493_);
v___x_2495_ = l_ReaderT_instMonad___redArg(v___x_2494_);
v___x_2496_ = l_StateRefT_x27_instMonad___redArg(v___x_2495_);
v___x_2497_ = l_ReaderT_instMonad___redArg(v___x_2496_);
v___x_2498_ = l_ReaderT_instMonad___redArg(v___x_2497_);
v___x_2499_ = l_StateRefT_x27_instMonad___redArg(v___x_2498_);
v___x_2500_ = l_ReaderT_instMonad___redArg(v___x_2499_);
v___x_2501_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16);
v_options_2502_ = lean_ctor_get(v_a_2430_, 2);
v_hasTrace_2503_ = lean_ctor_get_uint8(v_options_2502_, sizeof(void*)*1);
if (v_hasTrace_2503_ == 0)
{
lean_dec_ref(v___x_2500_);
v___y_2434_ = v_a_2422_;
goto v___jp_2433_;
}
else
{
lean_object* v_inheritedTraceOptions_2504_; lean_object* v_cls_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v_inheritedTraceOptions_2504_ = lean_ctor_get(v_a_2430_, 13);
v_cls_2505_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
v___x_2506_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___x_2507_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2504_, v_options_2502_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_dec_ref(v___x_2500_);
v___y_2434_ = v_a_2422_;
goto v___jp_2433_;
}
else
{
lean_object* v___x_2508_; lean_object* v_toMonadRef_2509_; lean_object* v_type_2510_; lean_object* v___f_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_6506__overap_2515_; lean_object* v___x_2516_; 
v___x_2508_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34);
v_toMonadRef_2509_ = lean_ctor_get(v___x_2508_, 0);
v_type_2510_ = lean_ctor_get(v_hyp_2420_, 1);
v___f_2511_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__41, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__41_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__41);
v___x_2512_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__43, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__43_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__43);
lean_inc_ref(v_type_2510_);
v___x_2513_ = l_Lean_MessageData_ofExpr(v_type_2510_);
v___x_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
lean_inc_ref(v_toMonadRef_2509_);
v___x_6506__overap_2515_ = l_Lean_addTrace___redArg(v___x_2500_, v___x_2501_, v_toMonadRef_2509_, v___f_2511_, v_cls_2505_, v___x_2514_);
lean_inc(v_a_2431_);
lean_inc_ref(v_a_2430_);
lean_inc(v_a_2429_);
lean_inc_ref(v_a_2428_);
lean_inc(v_a_2427_);
lean_inc_ref(v_a_2426_);
lean_inc(v_a_2425_);
lean_inc_ref(v_a_2424_);
lean_inc(v_a_2423_);
lean_inc(v_a_2422_);
lean_inc_ref(v_a_2421_);
v___x_2516_ = lean_apply_12(v___x_6506__overap_2515_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, lean_box(0));
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_dec_ref_known(v___x_2516_, 1);
v___y_2434_ = v_a_2422_;
goto v___jp_2433_;
}
else
{
lean_dec_ref(v_hyp_2420_);
return v___x_2516_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object* v_hyp_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(v_hyp_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object* v___x_2537_, lean_object* v___f_2538_, lean_object* v___x_2539_, lean_object* v___f_2540_, lean_object* v___x_2541_, lean_object* v___f_2542_, lean_object* v___f_2543_, lean_object* v___x_2544_, lean_object* v___f_2545_, lean_object* v___x_2546_, lean_object* v___x_2547_, lean_object* v_x_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_options_2565_; uint8_t v_hasTrace_2566_; 
v_options_2565_ = lean_ctor_get(v___y_2559_, 2);
v_hasTrace_2566_ = lean_ctor_get_uint8(v_options_2565_, sizeof(void*)*1);
if (v_hasTrace_2566_ == 0)
{
lean_dec_ref(v___y_2549_);
lean_dec_ref(v___x_2547_);
lean_dec_ref(v___x_2546_);
lean_dec(v___f_2545_);
lean_dec(v___x_2544_);
lean_dec(v___f_2543_);
lean_dec(v___f_2542_);
lean_dec(v___x_2541_);
lean_dec(v___f_2540_);
lean_dec(v___x_2539_);
lean_dec(v___f_2538_);
lean_dec(v___x_2537_);
goto v___jp_2562_;
}
else
{
lean_object* v_inheritedTraceOptions_2567_; lean_object* v_cls_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v_inheritedTraceOptions_2567_ = lean_ctor_get(v___y_2559_, 13);
v_cls_2568_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
v___x_2569_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___x_2570_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2567_, v_options_2565_, v___x_2569_);
if (v___x_2570_ == 0)
{
lean_dec_ref(v___y_2549_);
lean_dec_ref(v___x_2547_);
lean_dec_ref(v___x_2546_);
lean_dec(v___f_2545_);
lean_dec(v___x_2544_);
lean_dec(v___f_2543_);
lean_dec(v___f_2542_);
lean_dec(v___x_2541_);
lean_dec(v___f_2540_);
lean_dec(v___x_2539_);
lean_dec(v___f_2538_);
lean_dec(v___x_2537_);
goto v___jp_2562_;
}
else
{
lean_object* v___f_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v_toMonadRef_2583_; lean_object* v_type_2584_; lean_object* v___x_2585_; lean_object* v___f_2586_; lean_object* v___f_2587_; lean_object* v___f_2588_; lean_object* v___f_2589_; lean_object* v___f_2590_; lean_object* v___f_2591_; lean_object* v___f_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_7602__overap_2596_; lean_object* v___x_2597_; 
v___f_2571_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24));
v___x_2572_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25));
v___x_2573_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2574_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2572_, v___x_2537_, v___x_2573_);
v___x_2575_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2571_, v___f_2538_, v___x_2574_);
lean_inc(v___x_2539_);
v___x_2576_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2572_, v___x_2539_, v___x_2575_);
lean_inc(v___f_2540_);
v___x_2577_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2571_, v___f_2540_, v___x_2576_);
lean_inc(v___x_2541_);
v___x_2578_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2572_, v___x_2541_, v___x_2577_);
lean_inc(v___f_2542_);
v___x_2579_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2571_, v___f_2542_, v___x_2578_);
lean_inc(v___f_2543_);
v___x_2580_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2571_, v___f_2543_, v___x_2579_);
lean_inc(v___x_2544_);
v___x_2581_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2572_, v___x_2544_, v___x_2580_);
lean_inc(v___f_2545_);
v___x_2582_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2571_, v___f_2545_, v___x_2581_);
v_toMonadRef_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc_ref(v_toMonadRef_2583_);
lean_dec_ref(v___x_2582_);
v_type_2584_ = lean_ctor_get(v___y_2549_, 1);
lean_inc_ref(v_type_2584_);
lean_dec_ref(v___y_2549_);
v___x_2585_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2586_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2586_, 0, v___x_2585_);
lean_closure_set(v___f_2586_, 1, v___x_2539_);
v___f_2587_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2587_, 0, v___f_2586_);
lean_closure_set(v___f_2587_, 1, v___f_2540_);
v___f_2588_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2588_, 0, v___f_2587_);
lean_closure_set(v___f_2588_, 1, v___x_2541_);
v___f_2589_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2589_, 0, v___f_2588_);
lean_closure_set(v___f_2589_, 1, v___f_2542_);
v___f_2590_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2590_, 0, v___f_2589_);
lean_closure_set(v___f_2590_, 1, v___f_2543_);
v___f_2591_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2591_, 0, v___f_2590_);
lean_closure_set(v___f_2591_, 1, v___x_2544_);
v___f_2592_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2592_, 0, v___f_2591_);
lean_closure_set(v___f_2592_, 1, v___f_2545_);
v___x_2593_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__43, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__43_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__43);
v___x_2594_ = l_Lean_MessageData_ofExpr(v_type_2584_);
v___x_2595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2593_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_7602__overap_2596_ = l_Lean_addTrace___redArg(v___x_2546_, v___x_2547_, v_toMonadRef_2583_, v___f_2592_, v_cls_2568_, v___x_2595_);
lean_inc(v___y_2560_);
lean_inc_ref(v___y_2559_);
lean_inc(v___y_2558_);
lean_inc_ref(v___y_2557_);
lean_inc(v___y_2556_);
lean_inc_ref(v___y_2555_);
lean_inc(v___y_2554_);
lean_inc_ref(v___y_2553_);
lean_inc(v___y_2552_);
lean_inc(v___y_2551_);
lean_inc_ref(v___y_2550_);
v___x_2597_ = lean_apply_12(v___x_7602__overap_2596_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, lean_box(0));
return v___x_2597_;
}
}
v___jp_2562_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_box(0);
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
return v___x_2564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object** _args){
lean_object* v___x_2598_ = _args[0];
lean_object* v___f_2599_ = _args[1];
lean_object* v___x_2600_ = _args[2];
lean_object* v___f_2601_ = _args[3];
lean_object* v___x_2602_ = _args[4];
lean_object* v___f_2603_ = _args[5];
lean_object* v___f_2604_ = _args[6];
lean_object* v___x_2605_ = _args[7];
lean_object* v___f_2606_ = _args[8];
lean_object* v___x_2607_ = _args[9];
lean_object* v___x_2608_ = _args[10];
lean_object* v_x_2609_ = _args[11];
lean_object* v___y_2610_ = _args[12];
lean_object* v___y_2611_ = _args[13];
lean_object* v___y_2612_ = _args[14];
lean_object* v___y_2613_ = _args[15];
lean_object* v___y_2614_ = _args[16];
lean_object* v___y_2615_ = _args[17];
lean_object* v___y_2616_ = _args[18];
lean_object* v___y_2617_ = _args[19];
lean_object* v___y_2618_ = _args[20];
lean_object* v___y_2619_ = _args[21];
lean_object* v___y_2620_ = _args[22];
lean_object* v___y_2621_ = _args[23];
lean_object* v___y_2622_ = _args[24];
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(v___x_2598_, v___f_2599_, v___x_2600_, v___f_2601_, v___x_2602_, v___f_2603_, v___f_2604_, v___x_2605_, v___f_2606_, v___x_2607_, v___x_2608_, v_x_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object* v_hyps_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v___y_2658_; lean_object* v___x_2659_; lean_object* v_toApplicative_2660_; lean_object* v_toFunctor_2661_; lean_object* v_toSeq_2662_; lean_object* v_toSeqLeft_2663_; lean_object* v_toSeqRight_2664_; lean_object* v___f_2665_; lean_object* v___f_2666_; lean_object* v___f_2667_; lean_object* v___f_2668_; lean_object* v___x_2669_; lean_object* v___f_2670_; lean_object* v___f_2671_; lean_object* v___f_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v_toApplicative_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2727_; 
v___x_2659_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1);
v_toApplicative_2660_ = lean_ctor_get(v___x_2659_, 0);
v_toFunctor_2661_ = lean_ctor_get(v_toApplicative_2660_, 0);
v_toSeq_2662_ = lean_ctor_get(v_toApplicative_2660_, 2);
v_toSeqLeft_2663_ = lean_ctor_get(v_toApplicative_2660_, 3);
v_toSeqRight_2664_ = lean_ctor_get(v_toApplicative_2660_, 4);
v___f_2665_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2));
v___f_2666_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3));
lean_inc_ref_n(v_toFunctor_2661_, 2);
v___f_2667_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2667_, 0, v_toFunctor_2661_);
v___f_2668_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2668_, 0, v_toFunctor_2661_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___f_2667_);
lean_ctor_set(v___x_2669_, 1, v___f_2668_);
lean_inc(v_toSeqRight_2664_);
v___f_2670_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2670_, 0, v_toSeqRight_2664_);
lean_inc(v_toSeqLeft_2663_);
v___f_2671_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2671_, 0, v_toSeqLeft_2663_);
lean_inc(v_toSeq_2662_);
v___f_2672_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2672_, 0, v_toSeq_2662_);
v___x_2673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2669_);
lean_ctor_set(v___x_2673_, 1, v___f_2665_);
lean_ctor_set(v___x_2673_, 2, v___f_2672_);
lean_ctor_set(v___x_2673_, 3, v___f_2671_);
lean_ctor_set(v___x_2673_, 4, v___f_2670_);
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
lean_ctor_set(v___x_2674_, 1, v___f_2666_);
v___x_2675_ = l_StateRefT_x27_instMonad___redArg(v___x_2674_);
v_toApplicative_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; 
v_unused_2728_ = lean_ctor_get(v___x_2675_, 1);
lean_dec(v_unused_2728_);
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2727_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_toApplicative_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2727_;
goto v_resetjp_2677_;
}
v___jp_2637_:
{
lean_object* v___x_2638_; lean_object* v_rewriteSimpCache_2639_; lean_object* v_rewriteDSimpCache_2640_; lean_object* v_acCache_2641_; lean_object* v_typeAnalysis_2642_; lean_object* v_target_2643_; lean_object* v_hypotheses_2644_; uint8_t v_didChange_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2656_; 
v___x_2638_ = lean_st_ref_take(v_a_2626_);
v_rewriteSimpCache_2639_ = lean_ctor_get(v___x_2638_, 0);
v_rewriteDSimpCache_2640_ = lean_ctor_get(v___x_2638_, 1);
v_acCache_2641_ = lean_ctor_get(v___x_2638_, 2);
v_typeAnalysis_2642_ = lean_ctor_get(v___x_2638_, 3);
v_target_2643_ = lean_ctor_get(v___x_2638_, 4);
v_hypotheses_2644_ = lean_ctor_get(v___x_2638_, 5);
v_didChange_2645_ = lean_ctor_get_uint8(v___x_2638_, sizeof(void*)*6);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2647_ = v___x_2638_;
v_isShared_2648_ = v_isSharedCheck_2656_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_hypotheses_2644_);
lean_inc(v_target_2643_);
lean_inc(v_typeAnalysis_2642_);
lean_inc(v_acCache_2641_);
lean_inc(v_rewriteDSimpCache_2640_);
lean_inc(v_rewriteSimpCache_2639_);
lean_dec(v___x_2638_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2656_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = l_Array_append___redArg(v_hypotheses_2644_, v_hyps_2624_);
lean_dec_ref(v_hyps_2624_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 5, v___x_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_rewriteSimpCache_2639_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_rewriteDSimpCache_2640_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v_acCache_2641_);
lean_ctor_set(v_reuseFailAlloc_2655_, 3, v_typeAnalysis_2642_);
lean_ctor_set(v_reuseFailAlloc_2655_, 4, v_target_2643_);
lean_ctor_set(v_reuseFailAlloc_2655_, 5, v___x_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2655_, sizeof(void*)*6, v_didChange_2645_);
v___x_2651_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2652_ = lean_st_ref_set(v_a_2626_, v___x_2651_);
v___x_2653_ = lean_box(0);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
return v___x_2654_;
}
}
}
v___jp_2657_:
{
if (lean_obj_tag(v___y_2658_) == 0)
{
lean_dec_ref_known(v___y_2658_, 1);
goto v___jp_2637_;
}
else
{
lean_dec_ref(v_hyps_2624_);
return v___y_2658_;
}
}
v_resetjp_2677_:
{
lean_object* v_toFunctor_2680_; lean_object* v_toSeq_2681_; lean_object* v_toSeqLeft_2682_; lean_object* v_toSeqRight_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2725_; 
v_toFunctor_2680_ = lean_ctor_get(v_toApplicative_2676_, 0);
v_toSeq_2681_ = lean_ctor_get(v_toApplicative_2676_, 2);
v_toSeqLeft_2682_ = lean_ctor_get(v_toApplicative_2676_, 3);
v_toSeqRight_2683_ = lean_ctor_get(v_toApplicative_2676_, 4);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_toApplicative_2676_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v_toApplicative_2676_, 1);
lean_dec(v_unused_2726_);
v___x_2685_ = v_toApplicative_2676_;
v_isShared_2686_ = v_isSharedCheck_2725_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_toSeqRight_2683_);
lean_inc(v_toSeqLeft_2682_);
lean_inc(v_toSeq_2681_);
lean_inc(v_toFunctor_2680_);
lean_dec(v_toApplicative_2676_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2725_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___f_2687_; lean_object* v___f_2688_; lean_object* v___f_2689_; lean_object* v___f_2690_; lean_object* v___x_2691_; lean_object* v___f_2692_; lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___x_2696_; 
v___f_2687_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4));
v___f_2688_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5));
lean_inc_ref(v_toFunctor_2680_);
v___f_2689_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2689_, 0, v_toFunctor_2680_);
v___f_2690_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2690_, 0, v_toFunctor_2680_);
v___x_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___f_2689_);
lean_ctor_set(v___x_2691_, 1, v___f_2690_);
v___f_2692_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2692_, 0, v_toSeqRight_2683_);
v___f_2693_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2693_, 0, v_toSeqLeft_2682_);
v___f_2694_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2694_, 0, v_toSeq_2681_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 4, v___f_2692_);
lean_ctor_set(v___x_2685_, 3, v___f_2693_);
lean_ctor_set(v___x_2685_, 2, v___f_2694_);
lean_ctor_set(v___x_2685_, 1, v___f_2687_);
lean_ctor_set(v___x_2685_, 0, v___x_2691_);
v___x_2696_ = v___x_2685_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2691_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v___f_2687_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v___f_2694_);
lean_ctor_set(v_reuseFailAlloc_2724_, 3, v___f_2693_);
lean_ctor_set(v_reuseFailAlloc_2724_, 4, v___f_2692_);
v___x_2696_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___f_2688_);
lean_ctor_set(v___x_2678_, 0, v___x_2696_);
v___x_2698_ = v___x_2678_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v___f_2688_);
v___x_2698_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___f_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2699_ = l_StateRefT_x27_instMonad___redArg(v___x_2698_);
v___x_2700_ = l_ReaderT_instMonad___redArg(v___x_2699_);
v___x_2701_ = l_StateRefT_x27_instMonad___redArg(v___x_2700_);
v___x_2702_ = l_ReaderT_instMonad___redArg(v___x_2701_);
v___x_2703_ = l_ReaderT_instMonad___redArg(v___x_2702_);
v___x_2704_ = l_StateRefT_x27_instMonad___redArg(v___x_2703_);
v___x_2705_ = l_ReaderT_instMonad___redArg(v___x_2704_);
v___f_2706_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2707_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2708_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16);
v___x_2709_ = lean_unsigned_to_nat(0u);
v___x_2710_ = lean_array_get_size(v_hyps_2624_);
v___x_2711_ = lean_nat_dec_lt(v___x_2709_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_dec_ref(v___x_2705_);
goto v___jp_2637_;
}
else
{
lean_object* v___f_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
lean_inc_ref(v___x_2705_);
v___f_2712_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed), 25, 11);
lean_closure_set(v___f_2712_, 0, v___x_2707_);
lean_closure_set(v___f_2712_, 1, v___f_2706_);
lean_closure_set(v___f_2712_, 2, v___x_2707_);
lean_closure_set(v___f_2712_, 3, v___f_2706_);
lean_closure_set(v___f_2712_, 4, v___x_2707_);
lean_closure_set(v___f_2712_, 5, v___f_2706_);
lean_closure_set(v___f_2712_, 6, v___f_2706_);
lean_closure_set(v___f_2712_, 7, v___x_2707_);
lean_closure_set(v___f_2712_, 8, v___f_2706_);
lean_closure_set(v___f_2712_, 9, v___x_2705_);
lean_closure_set(v___f_2712_, 10, v___x_2708_);
v___x_2713_ = lean_box(0);
v___x_2714_ = lean_nat_dec_le(v___x_2710_, v___x_2710_);
if (v___x_2714_ == 0)
{
if (v___x_2711_ == 0)
{
lean_dec_ref(v___f_2712_);
lean_dec_ref(v___x_2705_);
goto v___jp_2637_;
}
else
{
size_t v___x_2715_; size_t v___x_2716_; lean_object* v___x_7158__overap_2717_; lean_object* v___x_2718_; 
v___x_2715_ = ((size_t)0ULL);
v___x_2716_ = lean_usize_of_nat(v___x_2710_);
lean_inc_ref(v_hyps_2624_);
v___x_7158__overap_2717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2705_, v___f_2712_, v_hyps_2624_, v___x_2715_, v___x_2716_, v___x_2713_);
lean_inc(v_a_2635_);
lean_inc_ref(v_a_2634_);
lean_inc(v_a_2633_);
lean_inc_ref(v_a_2632_);
lean_inc(v_a_2631_);
lean_inc_ref(v_a_2630_);
lean_inc(v_a_2629_);
lean_inc_ref(v_a_2628_);
lean_inc(v_a_2627_);
lean_inc(v_a_2626_);
lean_inc_ref(v_a_2625_);
v___x_2718_ = lean_apply_12(v___x_7158__overap_2717_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, lean_box(0));
v___y_2658_ = v___x_2718_;
goto v___jp_2657_;
}
}
else
{
size_t v___x_2719_; size_t v___x_2720_; lean_object* v___x_7162__overap_2721_; lean_object* v___x_2722_; 
v___x_2719_ = ((size_t)0ULL);
v___x_2720_ = lean_usize_of_nat(v___x_2710_);
lean_inc_ref(v_hyps_2624_);
v___x_7162__overap_2721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2705_, v___f_2712_, v_hyps_2624_, v___x_2719_, v___x_2720_, v___x_2713_);
lean_inc(v_a_2635_);
lean_inc_ref(v_a_2634_);
lean_inc(v_a_2633_);
lean_inc_ref(v_a_2632_);
lean_inc(v_a_2631_);
lean_inc_ref(v_a_2630_);
lean_inc(v_a_2629_);
lean_inc_ref(v_a_2628_);
lean_inc(v_a_2627_);
lean_inc(v_a_2626_);
lean_inc_ref(v_a_2625_);
v___x_2722_ = lean_apply_12(v___x_7162__overap_2721_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, lean_box(0));
v___y_2658_ = v___x_2722_;
goto v___jp_2657_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object* v_hyps_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_);
lean_dec(v_a_2740_);
lean_dec_ref(v_a_2739_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec(v_a_2731_);
lean_dec_ref(v_a_2730_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object* v_a_2743_){
_start:
{
lean_object* v___x_2745_; lean_object* v_hypotheses_2746_; lean_object* v___x_2747_; 
v___x_2745_ = lean_st_ref_get(v_a_2743_);
v_hypotheses_2746_ = lean_ctor_get(v___x_2745_, 5);
lean_inc_ref(v_hypotheses_2746_);
lean_dec(v___x_2745_);
v___x_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2747_, 0, v_hypotheses_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_2748_);
lean_dec(v_a_2748_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v___x_2763_; lean_object* v_hypotheses_2764_; lean_object* v___x_2765_; 
v___x_2763_ = lean_st_ref_get(v_a_2752_);
v_hypotheses_2764_ = lean_ctor_get(v___x_2763_, 5);
lean_inc_ref(v_hypotheses_2764_);
lean_dec(v___x_2763_);
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v_hypotheses_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
lean_dec(v_a_2770_);
lean_dec_ref(v_a_2769_);
lean_dec(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object* v_hyps_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___x_2792_; lean_object* v_rewriteSimpCache_2793_; lean_object* v_rewriteDSimpCache_2794_; lean_object* v_acCache_2795_; lean_object* v_typeAnalysis_2796_; lean_object* v_target_2797_; uint8_t v_didChange_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2808_; 
v___x_2792_ = lean_st_ref_take(v___y_2781_);
v_rewriteSimpCache_2793_ = lean_ctor_get(v___x_2792_, 0);
v_rewriteDSimpCache_2794_ = lean_ctor_get(v___x_2792_, 1);
v_acCache_2795_ = lean_ctor_get(v___x_2792_, 2);
v_typeAnalysis_2796_ = lean_ctor_get(v___x_2792_, 3);
v_target_2797_ = lean_ctor_get(v___x_2792_, 4);
v_didChange_2798_ = lean_ctor_get_uint8(v___x_2792_, sizeof(void*)*6);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2808_ == 0)
{
lean_object* v_unused_2809_; 
v_unused_2809_ = lean_ctor_get(v___x_2792_, 5);
lean_dec(v_unused_2809_);
v___x_2800_ = v___x_2792_;
v_isShared_2801_ = v_isSharedCheck_2808_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_target_2797_);
lean_inc(v_typeAnalysis_2796_);
lean_inc(v_acCache_2795_);
lean_inc(v_rewriteDSimpCache_2794_);
lean_inc(v_rewriteSimpCache_2793_);
lean_dec(v___x_2792_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2808_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 5, v_hyps_2779_);
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_rewriteSimpCache_2793_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v_rewriteDSimpCache_2794_);
lean_ctor_set(v_reuseFailAlloc_2807_, 2, v_acCache_2795_);
lean_ctor_set(v_reuseFailAlloc_2807_, 3, v_typeAnalysis_2796_);
lean_ctor_set(v_reuseFailAlloc_2807_, 4, v_target_2797_);
lean_ctor_set(v_reuseFailAlloc_2807_, 5, v_hyps_2779_);
lean_ctor_set_uint8(v_reuseFailAlloc_2807_, sizeof(void*)*6, v_didChange_2798_);
v___x_2803_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = lean_st_ref_set(v___y_2781_, v___x_2803_);
v___x_2805_ = lean_box(0);
v___x_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
return v___x_2806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object* v_hyps_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object* v_inst_2824_, lean_object* v_hyps_2825_){
_start:
{
lean_object* v___f_2826_; lean_object* v___x_2827_; 
v___f_2826_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2826_, 0, v_hyps_2825_);
v___x_2827_ = lean_apply_2(v_inst_2824_, lean_box(0), v___f_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2840_; lean_object* v_rewriteSimpCache_2841_; lean_object* v_rewriteDSimpCache_2842_; lean_object* v_acCache_2843_; lean_object* v_typeAnalysis_2844_; lean_object* v_target_2845_; uint8_t v_didChange_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2857_; 
v___x_2840_ = lean_st_ref_take(v___y_2829_);
v_rewriteSimpCache_2841_ = lean_ctor_get(v___x_2840_, 0);
v_rewriteDSimpCache_2842_ = lean_ctor_get(v___x_2840_, 1);
v_acCache_2843_ = lean_ctor_get(v___x_2840_, 2);
v_typeAnalysis_2844_ = lean_ctor_get(v___x_2840_, 3);
v_target_2845_ = lean_ctor_get(v___x_2840_, 4);
v_didChange_2846_ = lean_ctor_get_uint8(v___x_2840_, sizeof(void*)*6);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v___x_2840_, 5);
lean_dec(v_unused_2858_);
v___x_2848_ = v___x_2840_;
v_isShared_2849_ = v_isSharedCheck_2857_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_target_2845_);
lean_inc(v_typeAnalysis_2844_);
lean_inc(v_acCache_2843_);
lean_inc(v_rewriteDSimpCache_2842_);
lean_inc(v_rewriteSimpCache_2841_);
lean_dec(v___x_2840_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2857_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; lean_object* v___x_2852_; 
v___x_2850_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 5, v___x_2850_);
v___x_2852_ = v___x_2848_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_rewriteSimpCache_2841_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_rewriteDSimpCache_2842_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_acCache_2843_);
lean_ctor_set(v_reuseFailAlloc_2856_, 3, v_typeAnalysis_2844_);
lean_ctor_set(v_reuseFailAlloc_2856_, 4, v_target_2845_);
lean_ctor_set(v_reuseFailAlloc_2856_, 5, v___x_2850_);
lean_ctor_set_uint8(v_reuseFailAlloc_2856_, sizeof(void*)*6, v_didChange_2846_);
v___x_2852_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2853_ = lean_st_ref_set(v___y_2829_, v___x_2852_);
v___x_2854_ = lean_box(0);
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
return v___x_2855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object* v_toPure_2872_, lean_object* v_cls_2873_, lean_object* v_____do__lift_2874_, lean_object* v_____do__lift_2875_){
_start:
{
uint8_t v_hasTrace_2876_; 
v_hasTrace_2876_ = lean_ctor_get_uint8(v_____do__lift_2875_, sizeof(void*)*1);
if (v_hasTrace_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
lean_dec(v_cls_2873_);
v___x_2877_ = lean_box(v_hasTrace_2876_);
v___x_2878_ = lean_apply_2(v_toPure_2872_, lean_box(0), v___x_2877_);
return v___x_2878_;
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2879_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22));
v___x_2880_ = l_Lean_Name_append(v___x_2879_, v_cls_2873_);
v___x_2881_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2874_, v_____do__lift_2875_, v___x_2880_);
lean_dec(v___x_2880_);
v___x_2882_ = lean_box(v___x_2881_);
v___x_2883_ = lean_apply_2(v_toPure_2872_, lean_box(0), v___x_2882_);
return v___x_2883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object* v_toPure_2884_, lean_object* v_cls_2885_, lean_object* v_____do__lift_2886_, lean_object* v_____do__lift_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(v_toPure_2884_, v_cls_2885_, v_____do__lift_2886_, v_____do__lift_2887_);
lean_dec_ref(v_____do__lift_2887_);
lean_dec_ref(v_____do__lift_2886_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_toPure_2889_, lean_object* v_cls_2890_, lean_object* v_toBind_2891_, lean_object* v_inst_2892_, lean_object* v_____do__lift_2893_){
_start:
{
lean_object* v___f_2894_; lean_object* v___x_2895_; 
v___f_2894_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2894_, 0, v_toPure_2889_);
lean_closure_set(v___f_2894_, 1, v_cls_2890_);
lean_closure_set(v___f_2894_, 2, v_____do__lift_2893_);
v___x_2895_ = lean_apply_4(v_toBind_2891_, lean_box(0), lean_box(0), v_inst_2892_, v___f_2894_);
return v___x_2895_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0));
v___x_2898_ = l_Lean_stringToMessageData(v___x_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object* v_toPure_2899_, lean_object* v_a_2900_, lean_object* v___y_2901_, lean_object* v_inst_2902_, lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_cls_2906_, uint8_t v_____do__lift_2907_){
_start:
{
if (v_____do__lift_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
lean_dec(v_cls_2906_);
lean_dec(v_inst_2905_);
lean_dec_ref(v_inst_2904_);
lean_dec_ref(v_inst_2903_);
lean_dec_ref(v_inst_2902_);
lean_dec_ref(v___y_2901_);
lean_dec_ref(v_a_2900_);
v___x_2908_ = lean_box(0);
v___x_2909_ = lean_apply_2(v_toPure_2899_, lean_box(0), v___x_2908_);
return v___x_2909_;
}
else
{
lean_object* v_type_2910_; lean_object* v_type_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
lean_dec(v_toPure_2899_);
v_type_2910_ = lean_ctor_get(v_a_2900_, 1);
lean_inc_ref(v_type_2910_);
lean_dec_ref(v_a_2900_);
v_type_2911_ = lean_ctor_get(v___y_2901_, 1);
lean_inc_ref(v_type_2911_);
lean_dec_ref(v___y_2901_);
v___x_2912_ = l_Lean_MessageData_ofExpr(v_type_2910_);
v___x_2913_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_2914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2912_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = l_Lean_MessageData_ofExpr(v_type_2911_);
v___x_2916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2914_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = l_Lean_addTrace___redArg(v_inst_2902_, v_inst_2903_, v_inst_2904_, v_inst_2905_, v_cls_2906_, v___x_2916_);
return v___x_2917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object* v_toPure_2918_, lean_object* v_a_2919_, lean_object* v___y_2920_, lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_cls_2925_, lean_object* v_____do__lift_2926_){
_start:
{
uint8_t v_____do__lift_3364__boxed_2927_; lean_object* v_res_2928_; 
v_____do__lift_3364__boxed_2927_ = lean_unbox(v_____do__lift_2926_);
v_res_2928_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_2918_, v_a_2919_, v___y_2920_, v_inst_2921_, v_inst_2922_, v_inst_2923_, v_inst_2924_, v_cls_2925_, v_____do__lift_3364__boxed_2927_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_2929_, lean_object* v_toPure_2930_, lean_object* v_toBind_2931_, lean_object* v_inst_2932_, lean_object* v_a_2933_, lean_object* v_inst_2934_, lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_x_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_getInheritedTraceOptions_2939_; lean_object* v_cls_2940_; lean_object* v___f_2941_; lean_object* v___f_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v_getInheritedTraceOptions_2939_ = lean_ctor_get(v_inst_2929_, 2);
lean_inc(v_getInheritedTraceOptions_2939_);
v_cls_2940_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
lean_inc_n(v_toBind_2931_, 2);
lean_inc(v_toPure_2930_);
v___f_2941_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2941_, 0, v_toPure_2930_);
lean_closure_set(v___f_2941_, 1, v_cls_2940_);
lean_closure_set(v___f_2941_, 2, v_toBind_2931_);
lean_closure_set(v___f_2941_, 3, v_inst_2932_);
v___f_2942_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_2942_, 0, v_toPure_2930_);
lean_closure_set(v___f_2942_, 1, v_a_2933_);
lean_closure_set(v___f_2942_, 2, v___y_2938_);
lean_closure_set(v___f_2942_, 3, v_inst_2934_);
lean_closure_set(v___f_2942_, 4, v_inst_2929_);
lean_closure_set(v___f_2942_, 5, v_inst_2935_);
lean_closure_set(v___f_2942_, 6, v_inst_2936_);
lean_closure_set(v___f_2942_, 7, v_cls_2940_);
v___x_2943_ = lean_apply_4(v_toBind_2931_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2939_, v___f_2941_);
v___x_2944_ = lean_apply_4(v_toBind_2931_, lean_box(0), lean_box(0), v___x_2943_, v___f_2942_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object* v_toPure_2945_, lean_object* v_res_2946_, lean_object* v_____r_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = lean_apply_2(v_toPure_2945_, lean_box(0), v_res_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object* v_inst_2949_, lean_object* v_toBind_2950_, lean_object* v___f_2951_, lean_object* v_____r_2952_){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed), 12, 0);
v___x_2954_ = lean_apply_2(v_inst_2949_, lean_box(0), v___x_2953_);
v___x_2955_ = lean_apply_4(v_toBind_2950_, lean_box(0), lean_box(0), v___x_2954_, v___f_2951_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object* v___f_2956_, lean_object* v_____r_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = lean_apply_1(v___f_2956_, v_____r_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object* v___f_2959_, lean_object* v_type_2960_, lean_object* v_type_2961_, lean_object* v_inst_2962_, lean_object* v_inst_2963_, lean_object* v_inst_2964_, lean_object* v_inst_2965_, lean_object* v_cls_2966_, lean_object* v_toBind_2967_, lean_object* v___f_2968_, uint8_t v_____do__lift_2969_){
_start:
{
if (v_____do__lift_2969_ == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
lean_dec(v___f_2968_);
lean_dec(v_toBind_2967_);
lean_dec(v_cls_2966_);
lean_dec(v_inst_2965_);
lean_dec_ref(v_inst_2964_);
lean_dec_ref(v_inst_2963_);
lean_dec_ref(v_inst_2962_);
lean_dec_ref(v_type_2961_);
lean_dec_ref(v_type_2960_);
v___x_2970_ = lean_box(0);
v___x_2971_ = lean_apply_1(v___f_2959_, v___x_2970_);
return v___x_2971_;
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec(v___f_2959_);
v___x_2972_ = l_Lean_MessageData_ofExpr(v_type_2960_);
v___x_2973_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_2974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = l_Lean_MessageData_ofExpr(v_type_2961_);
v___x_2976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2974_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = l_Lean_addTrace___redArg(v_inst_2962_, v_inst_2963_, v_inst_2964_, v_inst_2965_, v_cls_2966_, v___x_2976_);
v___x_2978_ = lean_apply_4(v_toBind_2967_, lean_box(0), lean_box(0), v___x_2977_, v___f_2968_);
return v___x_2978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object* v___f_2979_, lean_object* v_type_2980_, lean_object* v_type_2981_, lean_object* v_inst_2982_, lean_object* v_inst_2983_, lean_object* v_inst_2984_, lean_object* v_inst_2985_, lean_object* v_cls_2986_, lean_object* v_toBind_2987_, lean_object* v___f_2988_, lean_object* v_____do__lift_2989_){
_start:
{
uint8_t v_____do__lift_3464__boxed_2990_; lean_object* v_res_2991_; 
v_____do__lift_3464__boxed_2990_ = lean_unbox(v_____do__lift_2989_);
v_res_2991_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_2979_, v_type_2980_, v_type_2981_, v_inst_2982_, v_inst_2983_, v_inst_2984_, v_inst_2985_, v_cls_2986_, v_toBind_2987_, v___f_2988_, v_____do__lift_3464__boxed_2990_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object* v_toPure_2992_, lean_object* v_inst_2993_, lean_object* v_toBind_2994_, lean_object* v_inst_2995_, lean_object* v___f_2996_, lean_object* v_a_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_inst_3001_, lean_object* v___f_3002_, lean_object* v_res_3003_){
_start:
{
lean_object* v___x_3004_; lean_object* v_zero_3005_; uint8_t v_isZero_3006_; 
v___x_3004_ = lean_array_get_size(v_res_3003_);
v_zero_3005_ = lean_unsigned_to_nat(0u);
v_isZero_3006_ = lean_nat_dec_eq(v___x_3004_, v_zero_3005_);
if (v_isZero_3006_ == 1)
{
lean_object* v___f_3007_; lean_object* v___f_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
lean_dec(v___f_3002_);
lean_dec(v_inst_3001_);
lean_dec_ref(v_inst_3000_);
lean_dec(v_inst_2999_);
lean_dec_ref(v_inst_2998_);
lean_dec_ref(v_a_2997_);
lean_inc_ref(v_res_3003_);
lean_inc(v_toPure_2992_);
v___f_3007_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3007_, 0, v_toPure_2992_);
lean_closure_set(v___f_3007_, 1, v_res_3003_);
lean_inc(v_toBind_2994_);
v___f_3008_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3008_, 0, v_inst_2993_);
lean_closure_set(v___f_3008_, 1, v_toBind_2994_);
lean_closure_set(v___f_3008_, 2, v___f_3007_);
v___x_3009_ = lean_box(0);
v___x_3010_ = lean_nat_dec_lt(v_zero_3005_, v___x_3004_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v_res_3003_);
lean_dec(v___f_2996_);
lean_dec_ref(v_inst_2995_);
v___x_3011_ = lean_apply_2(v_toPure_2992_, lean_box(0), v___x_3009_);
v___x_3012_ = lean_apply_4(v_toBind_2994_, lean_box(0), lean_box(0), v___x_3011_, v___f_3008_);
return v___x_3012_;
}
else
{
uint8_t v___x_3013_; 
v___x_3013_ = lean_nat_dec_le(v___x_3004_, v___x_3004_);
if (v___x_3013_ == 0)
{
if (v___x_3010_ == 0)
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
lean_dec_ref(v_res_3003_);
lean_dec(v___f_2996_);
lean_dec_ref(v_inst_2995_);
v___x_3014_ = lean_apply_2(v_toPure_2992_, lean_box(0), v___x_3009_);
v___x_3015_ = lean_apply_4(v_toBind_2994_, lean_box(0), lean_box(0), v___x_3014_, v___f_3008_);
return v___x_3015_;
}
else
{
size_t v___x_3016_; size_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
lean_dec(v_toPure_2992_);
v___x_3016_ = ((size_t)0ULL);
v___x_3017_ = lean_usize_of_nat(v___x_3004_);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2995_, v___f_2996_, v_res_3003_, v___x_3016_, v___x_3017_, v___x_3009_);
v___x_3019_ = lean_apply_4(v_toBind_2994_, lean_box(0), lean_box(0), v___x_3018_, v___f_3008_);
return v___x_3019_;
}
}
else
{
size_t v___x_3020_; size_t v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_dec(v_toPure_2992_);
v___x_3020_ = ((size_t)0ULL);
v___x_3021_ = lean_usize_of_nat(v___x_3004_);
v___x_3022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2995_, v___f_2996_, v_res_3003_, v___x_3020_, v___x_3021_, v___x_3009_);
v___x_3023_ = lean_apply_4(v_toBind_2994_, lean_box(0), lean_box(0), v___x_3022_, v___f_3008_);
return v___x_3023_;
}
}
}
else
{
lean_object* v_one_3024_; lean_object* v_n_3025_; uint8_t v_isZero_3026_; 
lean_dec(v___f_2996_);
v_one_3024_ = lean_unsigned_to_nat(1u);
v_n_3025_ = lean_nat_sub(v___x_3004_, v_one_3024_);
v_isZero_3026_ = lean_nat_dec_eq(v_n_3025_, v_zero_3005_);
lean_dec(v_n_3025_);
if (v_isZero_3026_ == 1)
{
lean_object* v_newHyp_3027_; lean_object* v_type_3028_; lean_object* v_type_3029_; uint8_t v___x_3030_; 
lean_dec(v___f_3002_);
v_newHyp_3027_ = lean_array_fget_borrowed(v_res_3003_, v_zero_3005_);
v_type_3028_ = lean_ctor_get(v_newHyp_3027_, 1);
v_type_3029_ = lean_ctor_get(v_a_2997_, 1);
lean_inc_ref(v_type_3029_);
lean_dec_ref(v_a_2997_);
v___x_3030_ = lean_expr_eqv(v_type_3028_, v_type_3029_);
if (v___x_3030_ == 0)
{
lean_object* v_getInheritedTraceOptions_3031_; lean_object* v___f_3032_; lean_object* v___f_3033_; lean_object* v___f_3034_; lean_object* v_cls_3035_; lean_object* v___f_3036_; lean_object* v___f_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_inc_ref(v_type_3028_);
v_getInheritedTraceOptions_3031_ = lean_ctor_get(v_inst_2998_, 2);
lean_inc(v_getInheritedTraceOptions_3031_);
lean_inc(v_toPure_2992_);
v___f_3032_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3032_, 0, v_toPure_2992_);
lean_closure_set(v___f_3032_, 1, v_res_3003_);
lean_inc_n(v_toBind_2994_, 4);
v___f_3033_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3033_, 0, v_inst_2993_);
lean_closure_set(v___f_3033_, 1, v_toBind_2994_);
lean_closure_set(v___f_3033_, 2, v___f_3032_);
lean_inc_ref(v___f_3033_);
v___f_3034_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3034_, 0, v___f_3033_);
v_cls_3035_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
v___f_3036_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_3036_, 0, v_toPure_2992_);
lean_closure_set(v___f_3036_, 1, v_cls_3035_);
lean_closure_set(v___f_3036_, 2, v_toBind_2994_);
lean_closure_set(v___f_3036_, 3, v_inst_2999_);
v___f_3037_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_3037_, 0, v___f_3033_);
lean_closure_set(v___f_3037_, 1, v_type_3029_);
lean_closure_set(v___f_3037_, 2, v_type_3028_);
lean_closure_set(v___f_3037_, 3, v_inst_2995_);
lean_closure_set(v___f_3037_, 4, v_inst_2998_);
lean_closure_set(v___f_3037_, 5, v_inst_3000_);
lean_closure_set(v___f_3037_, 6, v_inst_3001_);
lean_closure_set(v___f_3037_, 7, v_cls_3035_);
lean_closure_set(v___f_3037_, 8, v_toBind_2994_);
lean_closure_set(v___f_3037_, 9, v___f_3034_);
v___x_3038_ = lean_apply_4(v_toBind_2994_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3031_, v___f_3036_);
v___x_3039_ = lean_apply_4(v_toBind_2994_, lean_box(0), lean_box(0), v___x_3038_, v___f_3037_);
return v___x_3039_;
}
else
{
lean_object* v___x_3040_; 
lean_dec_ref(v_type_3029_);
lean_dec(v_inst_3001_);
lean_dec_ref(v_inst_3000_);
lean_dec(v_inst_2999_);
lean_dec_ref(v_inst_2998_);
lean_dec_ref(v_inst_2995_);
lean_dec(v_toBind_2994_);
lean_dec(v_inst_2993_);
v___x_3040_ = lean_apply_2(v_toPure_2992_, lean_box(0), v_res_3003_);
return v___x_3040_;
}
}
else
{
lean_object* v___f_3041_; lean_object* v___f_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
lean_dec(v_inst_3001_);
lean_dec_ref(v_inst_3000_);
lean_dec(v_inst_2999_);
lean_dec_ref(v_inst_2998_);
lean_dec_ref(v_a_2997_);
lean_inc_ref(v_res_3003_);
lean_inc(v_toPure_2992_);
v___f_3041_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_3041_, 0, v_toPure_2992_);
lean_closure_set(v___f_3041_, 1, v_res_3003_);
lean_inc(v_toBind_2994_);
v___f_3042_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3042_, 0, v_inst_2993_);
lean_closure_set(v___f_3042_, 1, v_toBind_2994_);
lean_closure_set(v___f_3042_, 2, v___f_3041_);
v___x_3043_ = lean_box(0);
v___x_3044_ = lean_nat_dec_lt(v_zero_3005_, v___x_3004_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_dec_ref(v_res_3003_);
lean_dec(v___f_3002_);
lean_dec_ref(v_inst_2995_);
v___x_3045_ = lean_apply_2(v_toPure_2992_, lean_box(0), v___x_3043_);
v___x_3046_ = lean_apply_4(v_toBind_2994_, lean_box(0), lean_box(0), v___x_3045_, v___f_3042_);
return v___x_3046_;
}
else
{
uint8_t v___x_3047_; 
v___x_3047_ = lean_nat_dec_le(v___x_3004_, v___x_3004_);
if (v___x_3047_ == 0)
{
if (v___x_3044_ == 0)
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
lean_dec_ref(v_res_3003_);
lean_dec(v___f_3002_);
lean_dec_ref(v_inst_2995_);
v___x_3048_ = lean_apply_2(v_toPure_2992_, lean_box(0), v___x_3043_);
v___x_3049_ = lean_apply_4(v_toBind_2994_, lean_box(0), lean_box(0), v___x_3048_, v___f_3042_);
return v___x_3049_;
}
else
{
size_t v___x_3050_; size_t v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_dec(v_toPure_2992_);
v___x_3050_ = ((size_t)0ULL);
v___x_3051_ = lean_usize_of_nat(v___x_3004_);
v___x_3052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2995_, v___f_3002_, v_res_3003_, v___x_3050_, v___x_3051_, v___x_3043_);
v___x_3053_ = lean_apply_4(v_toBind_2994_, lean_box(0), lean_box(0), v___x_3052_, v___f_3042_);
return v___x_3053_;
}
}
else
{
size_t v___x_3054_; size_t v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
lean_dec(v_toPure_2992_);
v___x_3054_ = ((size_t)0ULL);
v___x_3055_ = lean_usize_of_nat(v___x_3004_);
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2995_, v___f_3002_, v_res_3003_, v___x_3054_, v___x_3055_, v___x_3043_);
v___x_3057_ = lean_apply_4(v_toBind_2994_, lean_box(0), lean_box(0), v___x_3056_, v___f_3042_);
return v___x_3057_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object* v_bs_3058_, lean_object* v_toPure_3059_, lean_object* v_____do__lift_3060_){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = l_Array_append___redArg(v_bs_3058_, v_____do__lift_3060_);
v___x_3062_ = lean_apply_2(v_toPure_3059_, lean_box(0), v___x_3061_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object* v_bs_3063_, lean_object* v_toPure_3064_, lean_object* v_____do__lift_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(v_bs_3063_, v_toPure_3064_, v_____do__lift_3065_);
lean_dec_ref(v_____do__lift_3065_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_3067_, lean_object* v_toPure_3068_, lean_object* v_toBind_3069_, lean_object* v_inst_3070_, lean_object* v_inst_3071_, lean_object* v_inst_3072_, lean_object* v_inst_3073_, lean_object* v_inst_3074_, lean_object* v_f_3075_, lean_object* v_bs_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v___f_3078_; lean_object* v___f_3079_; lean_object* v___f_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_inc(v_inst_3073_);
lean_inc_ref(v_inst_3072_);
lean_inc_ref(v_inst_3071_);
lean_inc_ref_n(v_a_3077_, 2);
lean_inc(v_inst_3070_);
lean_inc_n(v_toBind_3069_, 3);
lean_inc_n(v_toPure_3068_, 2);
lean_inc_ref(v_inst_3067_);
v___f_3078_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_3078_, 0, v_inst_3067_);
lean_closure_set(v___f_3078_, 1, v_toPure_3068_);
lean_closure_set(v___f_3078_, 2, v_toBind_3069_);
lean_closure_set(v___f_3078_, 3, v_inst_3070_);
lean_closure_set(v___f_3078_, 4, v_a_3077_);
lean_closure_set(v___f_3078_, 5, v_inst_3071_);
lean_closure_set(v___f_3078_, 6, v_inst_3072_);
lean_closure_set(v___f_3078_, 7, v_inst_3073_);
lean_inc_ref(v___f_3078_);
v___f_3079_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_3079_, 0, v_toPure_3068_);
lean_closure_set(v___f_3079_, 1, v_inst_3074_);
lean_closure_set(v___f_3079_, 2, v_toBind_3069_);
lean_closure_set(v___f_3079_, 3, v_inst_3071_);
lean_closure_set(v___f_3079_, 4, v___f_3078_);
lean_closure_set(v___f_3079_, 5, v_a_3077_);
lean_closure_set(v___f_3079_, 6, v_inst_3067_);
lean_closure_set(v___f_3079_, 7, v_inst_3070_);
lean_closure_set(v___f_3079_, 8, v_inst_3072_);
lean_closure_set(v___f_3079_, 9, v_inst_3073_);
lean_closure_set(v___f_3079_, 10, v___f_3078_);
v___f_3080_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_3080_, 0, v_bs_3076_);
lean_closure_set(v___f_3080_, 1, v_toPure_3068_);
v___x_3081_ = lean_apply_1(v_f_3075_, v_a_3077_);
v___x_3082_ = lean_apply_4(v_toBind_3069_, lean_box(0), lean_box(0), v___x_3081_, v___f_3079_);
v___x_3083_ = lean_apply_4(v_toBind_3069_, lean_box(0), lean_box(0), v___x_3082_, v___f_3080_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object* v_hyps_3086_, lean_object* v_toPure_3087_, lean_object* v_toBind_3088_, lean_object* v___f_3089_, lean_object* v_inst_3090_, lean_object* v___f_3091_, lean_object* v_____r_3092_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
v___x_3093_ = lean_unsigned_to_nat(0u);
v___x_3094_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0));
v___x_3095_ = lean_array_get_size(v_hyps_3086_);
v___x_3096_ = lean_nat_dec_lt(v___x_3093_, v___x_3095_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
lean_dec(v___f_3091_);
lean_dec_ref(v_inst_3090_);
lean_dec_ref(v_hyps_3086_);
v___x_3097_ = lean_apply_2(v_toPure_3087_, lean_box(0), v___x_3094_);
v___x_3098_ = lean_apply_4(v_toBind_3088_, lean_box(0), lean_box(0), v___x_3097_, v___f_3089_);
return v___x_3098_;
}
else
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_nat_dec_le(v___x_3095_, v___x_3095_);
if (v___x_3099_ == 0)
{
if (v___x_3096_ == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
lean_dec(v___f_3091_);
lean_dec_ref(v_inst_3090_);
lean_dec_ref(v_hyps_3086_);
v___x_3100_ = lean_apply_2(v_toPure_3087_, lean_box(0), v___x_3094_);
v___x_3101_ = lean_apply_4(v_toBind_3088_, lean_box(0), lean_box(0), v___x_3100_, v___f_3089_);
return v___x_3101_;
}
else
{
size_t v___x_3102_; size_t v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_dec(v_toPure_3087_);
v___x_3102_ = ((size_t)0ULL);
v___x_3103_ = lean_usize_of_nat(v___x_3095_);
v___x_3104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3090_, v___f_3091_, v_hyps_3086_, v___x_3102_, v___x_3103_, v___x_3094_);
v___x_3105_ = lean_apply_4(v_toBind_3088_, lean_box(0), lean_box(0), v___x_3104_, v___f_3089_);
return v___x_3105_;
}
}
else
{
size_t v___x_3106_; size_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_dec(v_toPure_3087_);
v___x_3106_ = ((size_t)0ULL);
v___x_3107_ = lean_usize_of_nat(v___x_3095_);
v___x_3108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3090_, v___f_3091_, v_hyps_3086_, v___x_3106_, v___x_3107_, v___x_3094_);
v___x_3109_ = lean_apply_4(v_toBind_3088_, lean_box(0), lean_box(0), v___x_3108_, v___f_3089_);
return v___x_3109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object* v_toPure_3110_, lean_object* v_toBind_3111_, lean_object* v___f_3112_, lean_object* v_inst_3113_, lean_object* v___f_3114_, lean_object* v_inst_3115_, lean_object* v___f_3116_, lean_object* v_hyps_3117_){
_start:
{
lean_object* v___f_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_inc(v_toBind_3111_);
v___f_3118_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14), 7, 6);
lean_closure_set(v___f_3118_, 0, v_hyps_3117_);
lean_closure_set(v___f_3118_, 1, v_toPure_3110_);
lean_closure_set(v___f_3118_, 2, v_toBind_3111_);
lean_closure_set(v___f_3118_, 3, v___f_3112_);
lean_closure_set(v___f_3118_, 4, v_inst_3113_);
lean_closure_set(v___f_3118_, 5, v___f_3114_);
v___x_3119_ = lean_apply_2(v_inst_3115_, lean_box(0), v___f_3116_);
v___x_3120_ = lean_apply_4(v_toBind_3111_, lean_box(0), lean_box(0), v___x_3119_, v___f_3118_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object* v_inst_3122_, lean_object* v_inst_3123_, lean_object* v_inst_3124_, lean_object* v_inst_3125_, lean_object* v_inst_3126_, lean_object* v_inst_3127_, lean_object* v_f_3128_){
_start:
{
lean_object* v_toApplicative_3129_; lean_object* v_toBind_3130_; lean_object* v_toPure_3131_; lean_object* v___f_3132_; lean_object* v___f_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___f_3136_; lean_object* v___f_3137_; lean_object* v___x_3138_; 
v_toApplicative_3129_ = lean_ctor_get(v_inst_3122_, 0);
v_toBind_3130_ = lean_ctor_get(v_inst_3122_, 1);
lean_inc_n(v_toBind_3130_, 3);
v_toPure_3131_ = lean_ctor_get(v_toApplicative_3129_, 1);
lean_inc_n(v_toPure_3131_, 2);
lean_inc_n(v_inst_3127_, 3);
v___f_3132_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3132_, 0, v_inst_3127_);
v___f_3133_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3134_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3135_ = lean_apply_2(v_inst_3127_, lean_box(0), v___x_3134_);
lean_inc_ref(v_inst_3122_);
v___f_3136_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3136_, 0, v_inst_3123_);
lean_closure_set(v___f_3136_, 1, v_toPure_3131_);
lean_closure_set(v___f_3136_, 2, v_toBind_3130_);
lean_closure_set(v___f_3136_, 3, v_inst_3124_);
lean_closure_set(v___f_3136_, 4, v_inst_3122_);
lean_closure_set(v___f_3136_, 5, v_inst_3126_);
lean_closure_set(v___f_3136_, 6, v_inst_3125_);
lean_closure_set(v___f_3136_, 7, v_inst_3127_);
lean_closure_set(v___f_3136_, 8, v_f_3128_);
v___f_3137_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3137_, 0, v_toPure_3131_);
lean_closure_set(v___f_3137_, 1, v_toBind_3130_);
lean_closure_set(v___f_3137_, 2, v___f_3132_);
lean_closure_set(v___f_3137_, 3, v_inst_3122_);
lean_closure_set(v___f_3137_, 4, v___f_3136_);
lean_closure_set(v___f_3137_, 5, v_inst_3127_);
lean_closure_set(v___f_3137_, 6, v___f_3133_);
v___x_3138_ = lean_apply_4(v_toBind_3130_, lean_box(0), lean_box(0), v___x_3135_, v___f_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object* v_m_3139_, lean_object* v_inst_3140_, lean_object* v_inst_3141_, lean_object* v_inst_3142_, lean_object* v_inst_3143_, lean_object* v_inst_3144_, lean_object* v_inst_3145_, lean_object* v_f_3146_){
_start:
{
lean_object* v_toApplicative_3147_; lean_object* v_toBind_3148_; lean_object* v_toPure_3149_; lean_object* v___f_3150_; lean_object* v___f_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___f_3154_; lean_object* v___f_3155_; lean_object* v___x_3156_; 
v_toApplicative_3147_ = lean_ctor_get(v_inst_3140_, 0);
v_toBind_3148_ = lean_ctor_get(v_inst_3140_, 1);
lean_inc_n(v_toBind_3148_, 3);
v_toPure_3149_ = lean_ctor_get(v_toApplicative_3147_, 1);
lean_inc_n(v_toPure_3149_, 2);
lean_inc_n(v_inst_3145_, 3);
v___f_3150_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3150_, 0, v_inst_3145_);
v___f_3151_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3152_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3153_ = lean_apply_2(v_inst_3145_, lean_box(0), v___x_3152_);
lean_inc_ref(v_inst_3140_);
v___f_3154_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3154_, 0, v_inst_3141_);
lean_closure_set(v___f_3154_, 1, v_toPure_3149_);
lean_closure_set(v___f_3154_, 2, v_toBind_3148_);
lean_closure_set(v___f_3154_, 3, v_inst_3142_);
lean_closure_set(v___f_3154_, 4, v_inst_3140_);
lean_closure_set(v___f_3154_, 5, v_inst_3144_);
lean_closure_set(v___f_3154_, 6, v_inst_3143_);
lean_closure_set(v___f_3154_, 7, v_inst_3145_);
lean_closure_set(v___f_3154_, 8, v_f_3146_);
v___f_3155_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3155_, 0, v_toPure_3149_);
lean_closure_set(v___f_3155_, 1, v_toBind_3148_);
lean_closure_set(v___f_3155_, 2, v___f_3150_);
lean_closure_set(v___f_3155_, 3, v_inst_3140_);
lean_closure_set(v___f_3155_, 4, v___f_3154_);
lean_closure_set(v___f_3155_, 5, v_inst_3145_);
lean_closure_set(v___f_3155_, 6, v___f_3151_);
v___x_3156_ = lean_apply_4(v_toBind_3148_, lean_box(0), lean_box(0), v___x_3153_, v___f_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object* v_toPure_3157_, lean_object* v_____do__lift_3158_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_apply_2(v_toPure_3157_, lean_box(0), v_____do__lift_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object* v_toPure_3160_, lean_object* v_____r_3161_){
_start:
{
uint8_t v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = 0;
v___x_3163_ = lean_box(v___x_3162_);
v___x_3164_ = lean_apply_2(v_toPure_3160_, lean_box(0), v___x_3163_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object* v_snd_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___x_3178_; lean_object* v_rewriteSimpCache_3179_; lean_object* v_rewriteDSimpCache_3180_; lean_object* v_acCache_3181_; lean_object* v_typeAnalysis_3182_; lean_object* v_target_3183_; uint8_t v_didChange_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3194_; 
v___x_3178_ = lean_st_ref_take(v___y_3167_);
v_rewriteSimpCache_3179_ = lean_ctor_get(v___x_3178_, 0);
v_rewriteDSimpCache_3180_ = lean_ctor_get(v___x_3178_, 1);
v_acCache_3181_ = lean_ctor_get(v___x_3178_, 2);
v_typeAnalysis_3182_ = lean_ctor_get(v___x_3178_, 3);
v_target_3183_ = lean_ctor_get(v___x_3178_, 4);
v_didChange_3184_ = lean_ctor_get_uint8(v___x_3178_, sizeof(void*)*6);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; 
v_unused_3195_ = lean_ctor_get(v___x_3178_, 5);
lean_dec(v_unused_3195_);
v___x_3186_ = v___x_3178_;
v_isShared_3187_ = v_isSharedCheck_3194_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_target_3183_);
lean_inc(v_typeAnalysis_3182_);
lean_inc(v_acCache_3181_);
lean_inc(v_rewriteDSimpCache_3180_);
lean_inc(v_rewriteSimpCache_3179_);
lean_dec(v___x_3178_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3194_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 5, v_snd_3165_);
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_rewriteSimpCache_3179_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_rewriteDSimpCache_3180_);
lean_ctor_set(v_reuseFailAlloc_3193_, 2, v_acCache_3181_);
lean_ctor_set(v_reuseFailAlloc_3193_, 3, v_typeAnalysis_3182_);
lean_ctor_set(v_reuseFailAlloc_3193_, 4, v_target_3183_);
lean_ctor_set(v_reuseFailAlloc_3193_, 5, v_snd_3165_);
lean_ctor_set_uint8(v_reuseFailAlloc_3193_, sizeof(void*)*6, v_didChange_3184_);
v___x_3189_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3190_ = lean_st_ref_set(v___y_3167_, v___x_3189_);
v___x_3191_ = lean_box(0);
v___x_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
return v___x_3192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed(lean_object* v_snd_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(v_snd_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object* v_inst_3210_, lean_object* v_toBind_3211_, lean_object* v___f_3212_, lean_object* v_toPure_3213_, lean_object* v_____s_3214_){
_start:
{
lean_object* v_fst_3215_; 
v_fst_3215_ = lean_ctor_get(v_____s_3214_, 0);
if (lean_obj_tag(v_fst_3215_) == 0)
{
lean_object* v_snd_3216_; lean_object* v___f_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_dec(v_toPure_3213_);
v_snd_3216_ = lean_ctor_get(v_____s_3214_, 1);
lean_inc(v_snd_3216_);
lean_dec_ref(v_____s_3214_);
v___f_3217_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed), 13, 1);
lean_closure_set(v___f_3217_, 0, v_snd_3216_);
v___x_3218_ = lean_apply_2(v_inst_3210_, lean_box(0), v___f_3217_);
v___x_3219_ = lean_apply_4(v_toBind_3211_, lean_box(0), lean_box(0), v___x_3218_, v___f_3212_);
return v___x_3219_;
}
else
{
lean_object* v_val_3220_; lean_object* v___x_3221_; 
lean_inc_ref(v_fst_3215_);
lean_dec_ref(v_____s_3214_);
lean_dec(v___f_3212_);
lean_dec(v_toBind_3211_);
lean_dec(v_inst_3210_);
v_val_3220_ = lean_ctor_get(v_fst_3215_, 0);
lean_inc(v_val_3220_);
lean_dec_ref_known(v_fst_3215_, 1);
v___x_3221_ = lean_apply_2(v_toPure_3213_, lean_box(0), v_val_3220_);
return v___x_3221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object* v_toPure_3222_, lean_object* v_next_3223_, lean_object* v_G_3224_, lean_object* v_____do__lift_3225_){
_start:
{
if (lean_obj_tag(v_____do__lift_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3227_; 
lean_dec(v_G_3224_);
v_a_3226_ = lean_ctor_get(v_____do__lift_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v_____do__lift_3225_, 1);
v___x_3227_ = lean_apply_2(v_toPure_3222_, lean_box(0), v_a_3226_);
return v___x_3227_;
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_dec(v_toPure_3222_);
v_a_3228_ = lean_ctor_get(v_____do__lift_3225_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v_____do__lift_3225_, 1);
v___x_3229_ = lean_unsigned_to_nat(1u);
v___x_3230_ = lean_nat_add(v_next_3223_, v___x_3229_);
v___x_3231_ = lean_apply_4(v_G_3224_, v___x_3230_, v_a_3228_, lean_box(0), lean_box(0));
return v___x_3231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object* v_toPure_3232_, lean_object* v_next_3233_, lean_object* v_G_3234_, lean_object* v_____do__lift_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(v_toPure_3232_, v_next_3233_, v_G_3234_, v_____do__lift_3235_);
lean_dec(v_next_3233_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(lean_object* v_snd_3237_, lean_object* v_newHyp_3238_, lean_object* v___x_3239_, lean_object* v_toPure_3240_, lean_object* v_____r_3241_){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3242_ = lean_array_push(v_snd_3237_, v_newHyp_3238_);
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3239_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
v___x_3245_ = lean_apply_2(v_toPure_3240_, lean_box(0), v___x_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v_toPure_3246_, lean_object* v___x_3247_, lean_object* v_____do__lift_3248_, lean_object* v_____do__lift_3249_){
_start:
{
uint8_t v_hasTrace_3250_; 
v_hasTrace_3250_ = lean_ctor_get_uint8(v_____do__lift_3249_, sizeof(void*)*1);
if (v_hasTrace_3250_ == 0)
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_dec(v___x_3247_);
v___x_3251_ = lean_box(v_hasTrace_3250_);
v___x_3252_ = lean_apply_2(v_toPure_3246_, lean_box(0), v___x_3251_);
return v___x_3252_;
}
else
{
lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3253_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22));
v___x_3254_ = l_Lean_Name_append(v___x_3253_, v___x_3247_);
v___x_3255_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3248_, v_____do__lift_3249_, v___x_3254_);
lean_dec(v___x_3254_);
v___x_3256_ = lean_box(v___x_3255_);
v___x_3257_ = lean_apply_2(v_toPure_3246_, lean_box(0), v___x_3256_);
return v___x_3257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed(lean_object* v_toPure_3258_, lean_object* v___x_3259_, lean_object* v_____do__lift_3260_, lean_object* v_____do__lift_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(v_toPure_3258_, v___x_3259_, v_____do__lift_3260_, v_____do__lift_3261_);
lean_dec_ref(v_____do__lift_3261_);
lean_dec_ref(v_____do__lift_3260_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object* v_toPure_3263_, lean_object* v___x_3264_, lean_object* v_toBind_3265_, lean_object* v_inst_3266_, lean_object* v_____do__lift_3267_){
_start:
{
lean_object* v___f_3268_; lean_object* v___x_3269_; 
v___f_3268_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed), 4, 3);
lean_closure_set(v___f_3268_, 0, v_toPure_3263_);
lean_closure_set(v___f_3268_, 1, v___x_3264_);
lean_closure_set(v___f_3268_, 2, v_____do__lift_3267_);
v___x_3269_ = lean_apply_4(v_toBind_3265_, lean_box(0), lean_box(0), v_inst_3266_, v___f_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v___f_3270_, lean_object* v_inst_3271_, lean_object* v___x_3272_, lean_object* v_type_3273_, lean_object* v_inst_3274_, lean_object* v_inst_3275_, lean_object* v_inst_3276_, lean_object* v___x_3277_, lean_object* v_toBind_3278_, lean_object* v___f_3279_, uint8_t v_____do__lift_3280_){
_start:
{
if (v_____do__lift_3280_ == 0)
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
lean_dec(v___f_3279_);
lean_dec(v_toBind_3278_);
lean_dec(v___x_3277_);
lean_dec(v_inst_3276_);
lean_dec_ref(v_inst_3275_);
lean_dec_ref(v_inst_3274_);
lean_dec_ref(v_type_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_inst_3271_);
v___x_3281_ = lean_box(0);
v___x_3282_ = lean_apply_1(v___f_3270_, v___x_3281_);
return v___x_3282_;
}
else
{
lean_object* v_toMonadRef_3283_; lean_object* v_type_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
lean_dec(v___f_3270_);
v_toMonadRef_3283_ = lean_ctor_get(v_inst_3271_, 1);
lean_inc_ref(v_toMonadRef_3283_);
lean_dec_ref(v_inst_3271_);
v_type_3284_ = lean_ctor_get(v___x_3272_, 1);
lean_inc_ref(v_type_3284_);
lean_dec_ref(v___x_3272_);
v___x_3285_ = l_Lean_MessageData_ofExpr(v_type_3284_);
v___x_3286_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = l_Lean_MessageData_ofExpr(v_type_3273_);
v___x_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3287_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = l_Lean_addTrace___redArg(v_inst_3274_, v_inst_3275_, v_toMonadRef_3283_, v_inst_3276_, v___x_3277_, v___x_3289_);
v___x_3291_ = lean_apply_4(v_toBind_3278_, lean_box(0), lean_box(0), v___x_3290_, v___f_3279_);
return v___x_3291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed(lean_object* v___f_3292_, lean_object* v_inst_3293_, lean_object* v___x_3294_, lean_object* v_type_3295_, lean_object* v_inst_3296_, lean_object* v_inst_3297_, lean_object* v_inst_3298_, lean_object* v___x_3299_, lean_object* v_toBind_3300_, lean_object* v___f_3301_, lean_object* v_____do__lift_3302_){
_start:
{
uint8_t v_____do__lift_2152__boxed_3303_; lean_object* v_res_3304_; 
v_____do__lift_2152__boxed_3303_ = lean_unbox(v_____do__lift_3302_);
v_res_3304_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(v___f_3292_, v_inst_3293_, v___x_3294_, v_type_3295_, v_inst_3296_, v_inst_3297_, v_inst_3298_, v___x_3299_, v_toBind_3300_, v___f_3301_, v_____do__lift_2152__boxed_3303_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(uint8_t v___x_3305_, lean_object* v_snd_3306_, lean_object* v_toPure_3307_, lean_object* v_____r_3308_){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3309_ = lean_box(v___x_3305_);
v___x_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
v___x_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
lean_ctor_set(v___x_3311_, 1, v_snd_3306_);
v___x_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
v___x_3313_ = lean_apply_2(v_toPure_3307_, lean_box(0), v___x_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___x_3314_, lean_object* v_snd_3315_, lean_object* v_toPure_3316_, lean_object* v_____r_3317_){
_start:
{
uint8_t v___x_2190__boxed_3318_; lean_object* v_res_3319_; 
v___x_2190__boxed_3318_ = lean_unbox(v___x_3314_);
v_res_3319_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___x_2190__boxed_3318_, v_snd_3315_, v_toPure_3316_, v_____r_3317_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object* v_inst_3320_, lean_object* v_value_3321_, lean_object* v_toBind_3322_, lean_object* v___f_3323_, lean_object* v_____do__lift_3324_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = l_Lean_MVarId_assign___redArg(v_inst_3320_, v_____do__lift_3324_, v_value_3321_);
v___x_3326_ = lean_apply_4(v_toBind_3322_, lean_box(0), lean_box(0), v___x_3325_, v___f_3323_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_3327_, lean_object* v_snd_3328_, lean_object* v___x_3329_, lean_object* v_toPure_3330_, lean_object* v_inst_3331_, lean_object* v_toBind_3332_, lean_object* v_inst_3333_, lean_object* v_inst_3334_, lean_object* v_inst_3335_, lean_object* v_inst_3336_, lean_object* v_inst_3337_, lean_object* v_inst_3338_, lean_object* v_newHyp_3339_){
_start:
{
lean_object* v_type_3340_; lean_object* v_value_3341_; uint8_t v___x_3342_; 
v_type_3340_ = lean_ctor_get(v_newHyp_3339_, 1);
v_value_3341_ = lean_ctor_get(v_newHyp_3339_, 2);
lean_inc_ref(v_type_3340_);
v___x_3342_ = l_Lean_Expr_isFalse(v_type_3340_);
if (v___x_3342_ == 0)
{
lean_object* v_type_3343_; lean_object* v___f_3344_; lean_object* v___f_3345_; lean_object* v___f_3346_; lean_object* v___f_3347_; uint8_t v___x_3355_; 
lean_dec_ref(v_inst_3338_);
v_type_3343_ = lean_ctor_get(v___x_3327_, 1);
lean_inc(v_toPure_3330_);
lean_inc(v___x_3329_);
lean_inc_ref(v_newHyp_3339_);
lean_inc(v_snd_3328_);
v___f_3344_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5), 5, 4);
lean_closure_set(v___f_3344_, 0, v_snd_3328_);
lean_closure_set(v___f_3344_, 1, v_newHyp_3339_);
lean_closure_set(v___f_3344_, 2, v___x_3329_);
lean_closure_set(v___f_3344_, 3, v_toPure_3330_);
v___f_3345_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3345_, 0, v___f_3344_);
lean_inc(v_toBind_3332_);
v___f_3346_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3346_, 0, v_inst_3331_);
lean_closure_set(v___f_3346_, 1, v_toBind_3332_);
lean_closure_set(v___f_3346_, 2, v___f_3345_);
lean_inc_ref(v___f_3346_);
v___f_3347_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3347_, 0, v___f_3346_);
v___x_3355_ = lean_expr_eqv(v_type_3343_, v_type_3340_);
if (v___x_3355_ == 0)
{
lean_inc_ref(v_type_3340_);
lean_dec_ref(v_newHyp_3339_);
lean_dec(v___x_3329_);
lean_dec(v_snd_3328_);
goto v___jp_3348_;
}
else
{
if (v___x_3342_ == 0)
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
lean_dec_ref(v___f_3347_);
lean_dec_ref(v___f_3346_);
lean_dec(v_inst_3337_);
lean_dec_ref(v_inst_3336_);
lean_dec_ref(v_inst_3335_);
lean_dec(v_inst_3334_);
lean_dec_ref(v_inst_3333_);
lean_dec(v_toBind_3332_);
lean_dec_ref(v___x_3327_);
v___x_3356_ = lean_box(0);
v___x_3357_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v_snd_3328_, v_newHyp_3339_, v___x_3329_, v_toPure_3330_, v___x_3356_);
return v___x_3357_;
}
else
{
lean_inc_ref(v_type_3340_);
lean_dec_ref(v_newHyp_3339_);
lean_dec(v___x_3329_);
lean_dec(v_snd_3328_);
goto v___jp_3348_;
}
}
v___jp_3348_:
{
lean_object* v_getInheritedTraceOptions_3349_; lean_object* v___x_3350_; lean_object* v___f_3351_; lean_object* v___f_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v_getInheritedTraceOptions_3349_ = lean_ctor_get(v_inst_3333_, 2);
lean_inc(v_getInheritedTraceOptions_3349_);
v___x_3350_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
lean_inc_n(v_toBind_3332_, 3);
v___f_3351_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3351_, 0, v_toPure_3330_);
lean_closure_set(v___f_3351_, 1, v___x_3350_);
lean_closure_set(v___f_3351_, 2, v_toBind_3332_);
lean_closure_set(v___f_3351_, 3, v_inst_3334_);
v___f_3352_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed), 11, 10);
lean_closure_set(v___f_3352_, 0, v___f_3346_);
lean_closure_set(v___f_3352_, 1, v_inst_3335_);
lean_closure_set(v___f_3352_, 2, v___x_3327_);
lean_closure_set(v___f_3352_, 3, v_type_3340_);
lean_closure_set(v___f_3352_, 4, v_inst_3336_);
lean_closure_set(v___f_3352_, 5, v_inst_3333_);
lean_closure_set(v___f_3352_, 6, v_inst_3337_);
lean_closure_set(v___f_3352_, 7, v___x_3350_);
lean_closure_set(v___f_3352_, 8, v_toBind_3332_);
lean_closure_set(v___f_3352_, 9, v___f_3347_);
v___x_3353_ = lean_apply_4(v_toBind_3332_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3349_, v___f_3351_);
v___x_3354_ = lean_apply_4(v_toBind_3332_, lean_box(0), lean_box(0), v___x_3353_, v___f_3352_);
return v___x_3354_;
}
}
else
{
lean_object* v___x_3358_; lean_object* v___f_3359_; lean_object* v___f_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_inc_ref(v_value_3341_);
lean_dec_ref(v_newHyp_3339_);
lean_dec(v_inst_3337_);
lean_dec_ref(v_inst_3336_);
lean_dec_ref(v_inst_3335_);
lean_dec(v_inst_3334_);
lean_dec_ref(v_inst_3333_);
lean_dec(v___x_3329_);
lean_dec_ref(v___x_3327_);
v___x_3358_ = lean_box(v___x_3342_);
v___f_3359_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 4, 3);
lean_closure_set(v___f_3359_, 0, v___x_3358_);
lean_closure_set(v___f_3359_, 1, v_snd_3328_);
lean_closure_set(v___f_3359_, 2, v_toPure_3330_);
lean_inc(v_toBind_3332_);
v___f_3360_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10), 5, 4);
lean_closure_set(v___f_3360_, 0, v_inst_3338_);
lean_closure_set(v___f_3360_, 1, v_value_3341_);
lean_closure_set(v___f_3360_, 2, v_toBind_3332_);
lean_closure_set(v___f_3360_, 3, v___f_3359_);
v___x_3361_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___boxed), 12, 0);
v___x_3362_ = lean_apply_2(v_inst_3331_, lean_box(0), v___x_3361_);
v___x_3363_ = lean_apply_4(v_toBind_3332_, lean_box(0), lean_box(0), v___x_3362_, v___f_3360_);
return v___x_3363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v___x_3364_, lean_object* v_toPure_3365_, lean_object* v_hyps_3366_, lean_object* v___x_3367_, lean_object* v_inst_3368_, lean_object* v_toBind_3369_, lean_object* v_inst_3370_, lean_object* v_inst_3371_, lean_object* v_inst_3372_, lean_object* v_inst_3373_, lean_object* v_inst_3374_, lean_object* v_inst_3375_, lean_object* v_f_3376_, lean_object* v___f_3377_, lean_object* v_next_3378_, lean_object* v_acc_3379_, lean_object* v_h_3380_, lean_object* v_G_3381_){
_start:
{
uint8_t v___x_3382_; 
v___x_3382_ = lean_nat_dec_lt(v_next_3378_, v___x_3364_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3383_; 
lean_dec(v_G_3381_);
lean_dec(v_next_3378_);
lean_dec(v___f_3377_);
lean_dec(v_f_3376_);
lean_dec_ref(v_inst_3375_);
lean_dec(v_inst_3374_);
lean_dec_ref(v_inst_3373_);
lean_dec_ref(v_inst_3372_);
lean_dec(v_inst_3371_);
lean_dec_ref(v_inst_3370_);
lean_dec(v_toBind_3369_);
lean_dec(v_inst_3368_);
lean_dec(v___x_3367_);
v___x_3383_ = lean_apply_2(v_toPure_3365_, lean_box(0), v_acc_3379_);
return v___x_3383_;
}
else
{
lean_object* v_snd_3384_; lean_object* v___f_3385_; lean_object* v___x_3386_; lean_object* v___f_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v_snd_3384_ = lean_ctor_get(v_acc_3379_, 1);
lean_inc(v_snd_3384_);
lean_dec_ref(v_acc_3379_);
lean_inc(v_next_3378_);
lean_inc(v_toPure_3365_);
v___f_3385_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3385_, 0, v_toPure_3365_);
lean_closure_set(v___f_3385_, 1, v_next_3378_);
lean_closure_set(v___f_3385_, 2, v_G_3381_);
v___x_3386_ = lean_array_fget_borrowed(v_hyps_3366_, v_next_3378_);
lean_inc_n(v_toBind_3369_, 3);
lean_inc_n(v___x_3386_, 2);
v___f_3387_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11), 13, 12);
lean_closure_set(v___f_3387_, 0, v___x_3386_);
lean_closure_set(v___f_3387_, 1, v_snd_3384_);
lean_closure_set(v___f_3387_, 2, v___x_3367_);
lean_closure_set(v___f_3387_, 3, v_toPure_3365_);
lean_closure_set(v___f_3387_, 4, v_inst_3368_);
lean_closure_set(v___f_3387_, 5, v_toBind_3369_);
lean_closure_set(v___f_3387_, 6, v_inst_3370_);
lean_closure_set(v___f_3387_, 7, v_inst_3371_);
lean_closure_set(v___f_3387_, 8, v_inst_3372_);
lean_closure_set(v___f_3387_, 9, v_inst_3373_);
lean_closure_set(v___f_3387_, 10, v_inst_3374_);
lean_closure_set(v___f_3387_, 11, v_inst_3375_);
v___x_3388_ = lean_apply_2(v_f_3376_, v_next_3378_, v___x_3386_);
v___x_3389_ = lean_apply_4(v_toBind_3369_, lean_box(0), lean_box(0), v___x_3388_, v___f_3387_);
v___x_3390_ = lean_apply_4(v_toBind_3369_, lean_box(0), lean_box(0), v___x_3389_, v___f_3377_);
v___x_3391_ = lean_apply_4(v_toBind_3369_, lean_box(0), lean_box(0), v___x_3390_, v___f_3385_);
return v___x_3391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12___boxed(lean_object** _args){
lean_object* v___x_3392_ = _args[0];
lean_object* v_toPure_3393_ = _args[1];
lean_object* v_hyps_3394_ = _args[2];
lean_object* v___x_3395_ = _args[3];
lean_object* v_inst_3396_ = _args[4];
lean_object* v_toBind_3397_ = _args[5];
lean_object* v_inst_3398_ = _args[6];
lean_object* v_inst_3399_ = _args[7];
lean_object* v_inst_3400_ = _args[8];
lean_object* v_inst_3401_ = _args[9];
lean_object* v_inst_3402_ = _args[10];
lean_object* v_inst_3403_ = _args[11];
lean_object* v_f_3404_ = _args[12];
lean_object* v___f_3405_ = _args[13];
lean_object* v_next_3406_ = _args[14];
lean_object* v_acc_3407_ = _args[15];
lean_object* v_h_3408_ = _args[16];
lean_object* v_G_3409_ = _args[17];
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(v___x_3392_, v_toPure_3393_, v_hyps_3394_, v___x_3395_, v_inst_3396_, v_toBind_3397_, v_inst_3398_, v_inst_3399_, v_inst_3400_, v_inst_3401_, v_inst_3402_, v_inst_3403_, v_f_3404_, v___f_3405_, v_next_3406_, v_acc_3407_, v_h_3408_, v_G_3409_);
lean_dec_ref(v_hyps_3394_);
lean_dec(v___x_3392_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__13(lean_object* v_toPure_3411_, lean_object* v_inst_3412_, lean_object* v_toBind_3413_, lean_object* v_inst_3414_, lean_object* v_inst_3415_, lean_object* v_inst_3416_, lean_object* v_inst_3417_, lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_f_3420_, lean_object* v___f_3421_, lean_object* v___f_3422_, lean_object* v_hyps_3423_){
_start:
{
lean_object* v___x_3424_; lean_object* v_newHyps_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___f_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3424_ = lean_array_get_size(v_hyps_3423_);
v_newHyps_3425_ = lean_mk_empty_array_with_capacity(v___x_3424_);
v___x_3426_ = lean_unsigned_to_nat(0u);
v___x_3427_ = lean_box(0);
lean_inc(v_toBind_3413_);
v___f_3428_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12___boxed), 18, 14);
lean_closure_set(v___f_3428_, 0, v___x_3424_);
lean_closure_set(v___f_3428_, 1, v_toPure_3411_);
lean_closure_set(v___f_3428_, 2, v_hyps_3423_);
lean_closure_set(v___f_3428_, 3, v___x_3427_);
lean_closure_set(v___f_3428_, 4, v_inst_3412_);
lean_closure_set(v___f_3428_, 5, v_toBind_3413_);
lean_closure_set(v___f_3428_, 6, v_inst_3414_);
lean_closure_set(v___f_3428_, 7, v_inst_3415_);
lean_closure_set(v___f_3428_, 8, v_inst_3416_);
lean_closure_set(v___f_3428_, 9, v_inst_3417_);
lean_closure_set(v___f_3428_, 10, v_inst_3418_);
lean_closure_set(v___f_3428_, 11, v_inst_3419_);
lean_closure_set(v___f_3428_, 12, v_f_3420_);
lean_closure_set(v___f_3428_, 13, v___f_3421_);
v___x_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3427_);
lean_ctor_set(v___x_3429_, 1, v_newHyps_3425_);
v___x_3430_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3428_, v___x_3426_, v___x_3429_, lean_box(0));
v___x_3431_ = lean_apply_4(v_toBind_3413_, lean_box(0), lean_box(0), v___x_3430_, v___f_3422_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_3432_, lean_object* v_inst_3433_, lean_object* v_inst_3434_, lean_object* v_inst_3435_, lean_object* v_inst_3436_, lean_object* v_inst_3437_, lean_object* v_inst_3438_, lean_object* v_f_3439_){
_start:
{
lean_object* v_toApplicative_3440_; lean_object* v_toBind_3441_; lean_object* v_toPure_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___f_3445_; lean_object* v___f_3446_; lean_object* v___f_3447_; lean_object* v___f_3448_; lean_object* v___x_3449_; 
v_toApplicative_3440_ = lean_ctor_get(v_inst_3432_, 0);
v_toBind_3441_ = lean_ctor_get(v_inst_3432_, 1);
lean_inc_n(v_toBind_3441_, 3);
v_toPure_3442_ = lean_ctor_get(v_toApplicative_3440_, 1);
lean_inc_n(v_toPure_3442_, 4);
v___x_3443_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3433_, 2);
v___x_3444_ = lean_apply_2(v_inst_3433_, lean_box(0), v___x_3443_);
v___f_3445_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3445_, 0, v_toPure_3442_);
v___f_3446_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3446_, 0, v_toPure_3442_);
v___f_3447_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3447_, 0, v_inst_3433_);
lean_closure_set(v___f_3447_, 1, v_toBind_3441_);
lean_closure_set(v___f_3447_, 2, v___f_3446_);
lean_closure_set(v___f_3447_, 3, v_toPure_3442_);
v___f_3448_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3448_, 0, v_toPure_3442_);
lean_closure_set(v___f_3448_, 1, v_inst_3433_);
lean_closure_set(v___f_3448_, 2, v_toBind_3441_);
lean_closure_set(v___f_3448_, 3, v_inst_3436_);
lean_closure_set(v___f_3448_, 4, v_inst_3437_);
lean_closure_set(v___f_3448_, 5, v_inst_3434_);
lean_closure_set(v___f_3448_, 6, v_inst_3432_);
lean_closure_set(v___f_3448_, 7, v_inst_3438_);
lean_closure_set(v___f_3448_, 8, v_inst_3435_);
lean_closure_set(v___f_3448_, 9, v_f_3439_);
lean_closure_set(v___f_3448_, 10, v___f_3445_);
lean_closure_set(v___f_3448_, 11, v___f_3447_);
v___x_3449_ = lean_apply_4(v_toBind_3441_, lean_box(0), lean_box(0), v___x_3444_, v___f_3448_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_3450_, lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_inst_3453_, lean_object* v_inst_3454_, lean_object* v_inst_3455_, lean_object* v_inst_3456_, lean_object* v_inst_3457_, lean_object* v_inst_3458_, lean_object* v_f_3459_){
_start:
{
lean_object* v_toApplicative_3460_; lean_object* v_toBind_3461_; lean_object* v_toPure_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___f_3465_; lean_object* v___f_3466_; lean_object* v___f_3467_; lean_object* v___f_3468_; lean_object* v___x_3469_; 
v_toApplicative_3460_ = lean_ctor_get(v_inst_3451_, 0);
v_toBind_3461_ = lean_ctor_get(v_inst_3451_, 1);
lean_inc_n(v_toBind_3461_, 3);
v_toPure_3462_ = lean_ctor_get(v_toApplicative_3460_, 1);
lean_inc_n(v_toPure_3462_, 4);
v___x_3463_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3452_, 2);
v___x_3464_ = lean_apply_2(v_inst_3452_, lean_box(0), v___x_3463_);
v___f_3465_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3465_, 0, v_toPure_3462_);
v___f_3466_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3466_, 0, v_toPure_3462_);
v___f_3467_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3467_, 0, v_inst_3452_);
lean_closure_set(v___f_3467_, 1, v_toBind_3461_);
lean_closure_set(v___f_3467_, 2, v___f_3466_);
lean_closure_set(v___f_3467_, 3, v_toPure_3462_);
v___f_3468_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3468_, 0, v_toPure_3462_);
lean_closure_set(v___f_3468_, 1, v_inst_3452_);
lean_closure_set(v___f_3468_, 2, v_toBind_3461_);
lean_closure_set(v___f_3468_, 3, v_inst_3455_);
lean_closure_set(v___f_3468_, 4, v_inst_3456_);
lean_closure_set(v___f_3468_, 5, v_inst_3453_);
lean_closure_set(v___f_3468_, 6, v_inst_3451_);
lean_closure_set(v___f_3468_, 7, v_inst_3457_);
lean_closure_set(v___f_3468_, 8, v_inst_3454_);
lean_closure_set(v___f_3468_, 9, v_f_3459_);
lean_closure_set(v___f_3468_, 10, v___f_3465_);
lean_closure_set(v___f_3468_, 11, v___f_3467_);
v___x_3469_ = lean_apply_4(v_toBind_3461_, lean_box(0), lean_box(0), v___x_3464_, v___f_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object* v_m_3470_, lean_object* v_inst_3471_, lean_object* v_inst_3472_, lean_object* v_inst_3473_, lean_object* v_inst_3474_, lean_object* v_inst_3475_, lean_object* v_inst_3476_, lean_object* v_inst_3477_, lean_object* v_inst_3478_, lean_object* v_f_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(v_m_3470_, v_inst_3471_, v_inst_3472_, v_inst_3473_, v_inst_3474_, v_inst_3475_, v_inst_3476_, v_inst_3477_, v_inst_3478_, v_f_3479_);
lean_dec_ref(v_inst_3478_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__14(lean_object* v___x_3481_, lean_object* v_snd_3482_, lean_object* v___x_3483_, lean_object* v_toPure_3484_, lean_object* v_inst_3485_, lean_object* v_toBind_3486_, lean_object* v_inst_3487_, lean_object* v_inst_3488_, lean_object* v_inst_3489_, lean_object* v_inst_3490_, lean_object* v_inst_3491_, lean_object* v_inst_3492_, lean_object* v_newHyp_3493_){
_start:
{
lean_object* v_type_3494_; lean_object* v_value_3495_; uint8_t v___x_3496_; 
v_type_3494_ = lean_ctor_get(v_newHyp_3493_, 1);
v_value_3495_ = lean_ctor_get(v_newHyp_3493_, 2);
lean_inc_ref(v_type_3494_);
v___x_3496_ = l_Lean_Expr_isFalse(v_type_3494_);
if (v___x_3496_ == 0)
{
lean_object* v_type_3497_; lean_object* v___f_3498_; lean_object* v___f_3499_; lean_object* v___f_3500_; lean_object* v___f_3501_; uint8_t v___x_3509_; 
lean_dec_ref(v_inst_3492_);
v_type_3497_ = lean_ctor_get(v___x_3481_, 1);
lean_inc(v_toPure_3484_);
lean_inc(v___x_3483_);
lean_inc_ref(v_newHyp_3493_);
lean_inc(v_snd_3482_);
v___f_3498_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5), 5, 4);
lean_closure_set(v___f_3498_, 0, v_snd_3482_);
lean_closure_set(v___f_3498_, 1, v_newHyp_3493_);
lean_closure_set(v___f_3498_, 2, v___x_3483_);
lean_closure_set(v___f_3498_, 3, v_toPure_3484_);
v___f_3499_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3499_, 0, v___f_3498_);
lean_inc(v_toBind_3486_);
v___f_3500_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3500_, 0, v_inst_3485_);
lean_closure_set(v___f_3500_, 1, v_toBind_3486_);
lean_closure_set(v___f_3500_, 2, v___f_3499_);
lean_inc_ref(v___f_3500_);
v___f_3501_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3501_, 0, v___f_3500_);
v___x_3509_ = lean_expr_eqv(v_type_3497_, v_type_3494_);
if (v___x_3509_ == 0)
{
lean_inc_ref(v_type_3494_);
lean_dec_ref(v_newHyp_3493_);
lean_dec(v___x_3483_);
lean_dec(v_snd_3482_);
goto v___jp_3502_;
}
else
{
if (v___x_3496_ == 0)
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
lean_dec_ref(v___f_3501_);
lean_dec_ref(v___f_3500_);
lean_dec(v_inst_3491_);
lean_dec(v_inst_3490_);
lean_dec_ref(v_inst_3489_);
lean_dec_ref(v_inst_3488_);
lean_dec_ref(v_inst_3487_);
lean_dec(v_toBind_3486_);
lean_dec_ref(v___x_3481_);
v___x_3510_ = lean_box(0);
v___x_3511_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v_snd_3482_, v_newHyp_3493_, v___x_3483_, v_toPure_3484_, v___x_3510_);
return v___x_3511_;
}
else
{
lean_inc_ref(v_type_3494_);
lean_dec_ref(v_newHyp_3493_);
lean_dec(v___x_3483_);
lean_dec(v_snd_3482_);
goto v___jp_3502_;
}
}
v___jp_3502_:
{
lean_object* v_getInheritedTraceOptions_3503_; lean_object* v___x_3504_; lean_object* v___f_3505_; lean_object* v___f_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v_getInheritedTraceOptions_3503_ = lean_ctor_get(v_inst_3487_, 2);
lean_inc(v_getInheritedTraceOptions_3503_);
v___x_3504_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
lean_inc_n(v_toBind_3486_, 3);
v___f_3505_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed), 11, 10);
lean_closure_set(v___f_3505_, 0, v___f_3500_);
lean_closure_set(v___f_3505_, 1, v_inst_3488_);
lean_closure_set(v___f_3505_, 2, v___x_3481_);
lean_closure_set(v___f_3505_, 3, v_type_3494_);
lean_closure_set(v___f_3505_, 4, v_inst_3489_);
lean_closure_set(v___f_3505_, 5, v_inst_3487_);
lean_closure_set(v___f_3505_, 6, v_inst_3490_);
lean_closure_set(v___f_3505_, 7, v___x_3504_);
lean_closure_set(v___f_3505_, 8, v_toBind_3486_);
lean_closure_set(v___f_3505_, 9, v___f_3501_);
v___f_3506_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3506_, 0, v_toPure_3484_);
lean_closure_set(v___f_3506_, 1, v___x_3504_);
lean_closure_set(v___f_3506_, 2, v_toBind_3486_);
lean_closure_set(v___f_3506_, 3, v_inst_3491_);
v___x_3507_ = lean_apply_4(v_toBind_3486_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3503_, v___f_3506_);
v___x_3508_ = lean_apply_4(v_toBind_3486_, lean_box(0), lean_box(0), v___x_3507_, v___f_3505_);
return v___x_3508_;
}
}
else
{
lean_object* v___x_3512_; lean_object* v___f_3513_; lean_object* v___f_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
lean_inc_ref(v_value_3495_);
lean_dec_ref(v_newHyp_3493_);
lean_dec(v_inst_3491_);
lean_dec(v_inst_3490_);
lean_dec_ref(v_inst_3489_);
lean_dec_ref(v_inst_3488_);
lean_dec_ref(v_inst_3487_);
lean_dec(v___x_3483_);
lean_dec_ref(v___x_3481_);
v___x_3512_ = lean_box(v___x_3496_);
v___f_3513_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 4, 3);
lean_closure_set(v___f_3513_, 0, v___x_3512_);
lean_closure_set(v___f_3513_, 1, v_snd_3482_);
lean_closure_set(v___f_3513_, 2, v_toPure_3484_);
lean_inc(v_toBind_3486_);
v___f_3514_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10), 5, 4);
lean_closure_set(v___f_3514_, 0, v_inst_3492_);
lean_closure_set(v___f_3514_, 1, v_value_3495_);
lean_closure_set(v___f_3514_, 2, v_toBind_3486_);
lean_closure_set(v___f_3514_, 3, v___f_3513_);
v___x_3515_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTargetMVarId___boxed), 12, 0);
v___x_3516_ = lean_apply_2(v_inst_3485_, lean_box(0), v___x_3515_);
v___x_3517_ = lean_apply_4(v_toBind_3486_, lean_box(0), lean_box(0), v___x_3516_, v___f_3514_);
return v___x_3517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_3518_, lean_object* v_toPure_3519_, lean_object* v_hyps_3520_, lean_object* v___x_3521_, lean_object* v_inst_3522_, lean_object* v_toBind_3523_, lean_object* v_inst_3524_, lean_object* v_inst_3525_, lean_object* v_inst_3526_, lean_object* v_inst_3527_, lean_object* v_inst_3528_, lean_object* v_inst_3529_, lean_object* v_f_3530_, lean_object* v___f_3531_, lean_object* v_next_3532_, lean_object* v_acc_3533_, lean_object* v_h_3534_, lean_object* v_G_3535_){
_start:
{
uint8_t v___x_3536_; 
v___x_3536_ = lean_nat_dec_lt(v_next_3532_, v___x_3518_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
lean_dec(v_G_3535_);
lean_dec(v_next_3532_);
lean_dec(v___f_3531_);
lean_dec(v_f_3530_);
lean_dec_ref(v_inst_3529_);
lean_dec(v_inst_3528_);
lean_dec(v_inst_3527_);
lean_dec_ref(v_inst_3526_);
lean_dec_ref(v_inst_3525_);
lean_dec_ref(v_inst_3524_);
lean_dec(v_toBind_3523_);
lean_dec(v_inst_3522_);
lean_dec(v___x_3521_);
v___x_3537_ = lean_apply_2(v_toPure_3519_, lean_box(0), v_acc_3533_);
return v___x_3537_;
}
else
{
lean_object* v_snd_3538_; lean_object* v___f_3539_; lean_object* v___x_3540_; lean_object* v___f_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v_snd_3538_ = lean_ctor_get(v_acc_3533_, 1);
lean_inc(v_snd_3538_);
lean_dec_ref(v_acc_3533_);
lean_inc(v_next_3532_);
lean_inc(v_toPure_3519_);
v___f_3539_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3539_, 0, v_toPure_3519_);
lean_closure_set(v___f_3539_, 1, v_next_3532_);
lean_closure_set(v___f_3539_, 2, v_G_3535_);
v___x_3540_ = lean_array_fget_borrowed(v_hyps_3520_, v_next_3532_);
lean_dec(v_next_3532_);
lean_inc_n(v_toBind_3523_, 3);
lean_inc_n(v___x_3540_, 2);
v___f_3541_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__14), 13, 12);
lean_closure_set(v___f_3541_, 0, v___x_3540_);
lean_closure_set(v___f_3541_, 1, v_snd_3538_);
lean_closure_set(v___f_3541_, 2, v___x_3521_);
lean_closure_set(v___f_3541_, 3, v_toPure_3519_);
lean_closure_set(v___f_3541_, 4, v_inst_3522_);
lean_closure_set(v___f_3541_, 5, v_toBind_3523_);
lean_closure_set(v___f_3541_, 6, v_inst_3524_);
lean_closure_set(v___f_3541_, 7, v_inst_3525_);
lean_closure_set(v___f_3541_, 8, v_inst_3526_);
lean_closure_set(v___f_3541_, 9, v_inst_3527_);
lean_closure_set(v___f_3541_, 10, v_inst_3528_);
lean_closure_set(v___f_3541_, 11, v_inst_3529_);
v___x_3542_ = lean_apply_1(v_f_3530_, v___x_3540_);
v___x_3543_ = lean_apply_4(v_toBind_3523_, lean_box(0), lean_box(0), v___x_3542_, v___f_3541_);
v___x_3544_ = lean_apply_4(v_toBind_3523_, lean_box(0), lean_box(0), v___x_3543_, v___f_3531_);
v___x_3545_ = lean_apply_4(v_toBind_3523_, lean_box(0), lean_box(0), v___x_3544_, v___f_3539_);
return v___x_3545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3546_ = _args[0];
lean_object* v_toPure_3547_ = _args[1];
lean_object* v_hyps_3548_ = _args[2];
lean_object* v___x_3549_ = _args[3];
lean_object* v_inst_3550_ = _args[4];
lean_object* v_toBind_3551_ = _args[5];
lean_object* v_inst_3552_ = _args[6];
lean_object* v_inst_3553_ = _args[7];
lean_object* v_inst_3554_ = _args[8];
lean_object* v_inst_3555_ = _args[9];
lean_object* v_inst_3556_ = _args[10];
lean_object* v_inst_3557_ = _args[11];
lean_object* v_f_3558_ = _args[12];
lean_object* v___f_3559_ = _args[13];
lean_object* v_next_3560_ = _args[14];
lean_object* v_acc_3561_ = _args[15];
lean_object* v_h_3562_ = _args[16];
lean_object* v_G_3563_ = _args[17];
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3546_, v_toPure_3547_, v_hyps_3548_, v___x_3549_, v_inst_3550_, v_toBind_3551_, v_inst_3552_, v_inst_3553_, v_inst_3554_, v_inst_3555_, v_inst_3556_, v_inst_3557_, v_f_3558_, v___f_3559_, v_next_3560_, v_acc_3561_, v_h_3562_, v_G_3563_);
lean_dec_ref(v_hyps_3548_);
lean_dec(v___x_3546_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_3565_, lean_object* v_inst_3566_, lean_object* v_toBind_3567_, lean_object* v_inst_3568_, lean_object* v_inst_3569_, lean_object* v_inst_3570_, lean_object* v_inst_3571_, lean_object* v_inst_3572_, lean_object* v_inst_3573_, lean_object* v_f_3574_, lean_object* v___f_3575_, lean_object* v___f_3576_, lean_object* v_hyps_3577_){
_start:
{
lean_object* v___x_3578_; lean_object* v_newHyps_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___f_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3578_ = lean_array_get_size(v_hyps_3577_);
v_newHyps_3579_ = lean_mk_empty_array_with_capacity(v___x_3578_);
v___x_3580_ = lean_unsigned_to_nat(0u);
v___x_3581_ = lean_box(0);
lean_inc(v_toBind_3567_);
v___f_3582_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 18, 14);
lean_closure_set(v___f_3582_, 0, v___x_3578_);
lean_closure_set(v___f_3582_, 1, v_toPure_3565_);
lean_closure_set(v___f_3582_, 2, v_hyps_3577_);
lean_closure_set(v___f_3582_, 3, v___x_3581_);
lean_closure_set(v___f_3582_, 4, v_inst_3566_);
lean_closure_set(v___f_3582_, 5, v_toBind_3567_);
lean_closure_set(v___f_3582_, 6, v_inst_3568_);
lean_closure_set(v___f_3582_, 7, v_inst_3569_);
lean_closure_set(v___f_3582_, 8, v_inst_3570_);
lean_closure_set(v___f_3582_, 9, v_inst_3571_);
lean_closure_set(v___f_3582_, 10, v_inst_3572_);
lean_closure_set(v___f_3582_, 11, v_inst_3573_);
lean_closure_set(v___f_3582_, 12, v_f_3574_);
lean_closure_set(v___f_3582_, 13, v___f_3575_);
v___x_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3581_);
lean_ctor_set(v___x_3583_, 1, v_newHyps_3579_);
v___x_3584_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3582_, v___x_3580_, v___x_3583_, lean_box(0));
v___x_3585_ = lean_apply_4(v_toBind_3567_, lean_box(0), lean_box(0), v___x_3584_, v___f_3576_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_3586_, lean_object* v_inst_3587_, lean_object* v_inst_3588_, lean_object* v_inst_3589_, lean_object* v_inst_3590_, lean_object* v_inst_3591_, lean_object* v_inst_3592_, lean_object* v_f_3593_){
_start:
{
lean_object* v_toApplicative_3594_; lean_object* v_toBind_3595_; lean_object* v_toPure_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___f_3599_; lean_object* v___f_3600_; lean_object* v___f_3601_; lean_object* v___f_3602_; lean_object* v___x_3603_; 
v_toApplicative_3594_ = lean_ctor_get(v_inst_3586_, 0);
v_toBind_3595_ = lean_ctor_get(v_inst_3586_, 1);
lean_inc_n(v_toBind_3595_, 3);
v_toPure_3596_ = lean_ctor_get(v_toApplicative_3594_, 1);
lean_inc_n(v_toPure_3596_, 4);
v___x_3597_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3587_, 2);
v___x_3598_ = lean_apply_2(v_inst_3587_, lean_box(0), v___x_3597_);
v___f_3599_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3599_, 0, v_toPure_3596_);
v___f_3600_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3600_, 0, v_inst_3587_);
lean_closure_set(v___f_3600_, 1, v_toBind_3595_);
lean_closure_set(v___f_3600_, 2, v___f_3599_);
lean_closure_set(v___f_3600_, 3, v_toPure_3596_);
v___f_3601_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3601_, 0, v_toPure_3596_);
v___f_3602_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 13, 12);
lean_closure_set(v___f_3602_, 0, v_toPure_3596_);
lean_closure_set(v___f_3602_, 1, v_inst_3587_);
lean_closure_set(v___f_3602_, 2, v_toBind_3595_);
lean_closure_set(v___f_3602_, 3, v_inst_3590_);
lean_closure_set(v___f_3602_, 4, v_inst_3588_);
lean_closure_set(v___f_3602_, 5, v_inst_3586_);
lean_closure_set(v___f_3602_, 6, v_inst_3592_);
lean_closure_set(v___f_3602_, 7, v_inst_3591_);
lean_closure_set(v___f_3602_, 8, v_inst_3589_);
lean_closure_set(v___f_3602_, 9, v_f_3593_);
lean_closure_set(v___f_3602_, 10, v___f_3601_);
lean_closure_set(v___f_3602_, 11, v___f_3600_);
v___x_3603_ = lean_apply_4(v_toBind_3595_, lean_box(0), lean_box(0), v___x_3598_, v___f_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_3604_, lean_object* v_inst_3605_, lean_object* v_inst_3606_, lean_object* v_inst_3607_, lean_object* v_inst_3608_, lean_object* v_inst_3609_, lean_object* v_inst_3610_, lean_object* v_inst_3611_, lean_object* v_inst_3612_, lean_object* v_f_3613_){
_start:
{
lean_object* v_toApplicative_3614_; lean_object* v_toBind_3615_; lean_object* v_toPure_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___f_3619_; lean_object* v___f_3620_; lean_object* v___f_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; 
v_toApplicative_3614_ = lean_ctor_get(v_inst_3605_, 0);
v_toBind_3615_ = lean_ctor_get(v_inst_3605_, 1);
lean_inc_n(v_toBind_3615_, 3);
v_toPure_3616_ = lean_ctor_get(v_toApplicative_3614_, 1);
lean_inc_n(v_toPure_3616_, 4);
v___x_3617_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
lean_inc_n(v_inst_3606_, 2);
v___x_3618_ = lean_apply_2(v_inst_3606_, lean_box(0), v___x_3617_);
v___f_3619_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3619_, 0, v_toPure_3616_);
v___f_3620_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3620_, 0, v_inst_3606_);
lean_closure_set(v___f_3620_, 1, v_toBind_3615_);
lean_closure_set(v___f_3620_, 2, v___f_3619_);
lean_closure_set(v___f_3620_, 3, v_toPure_3616_);
v___f_3621_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3621_, 0, v_toPure_3616_);
v___f_3622_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 13, 12);
lean_closure_set(v___f_3622_, 0, v_toPure_3616_);
lean_closure_set(v___f_3622_, 1, v_inst_3606_);
lean_closure_set(v___f_3622_, 2, v_toBind_3615_);
lean_closure_set(v___f_3622_, 3, v_inst_3609_);
lean_closure_set(v___f_3622_, 4, v_inst_3607_);
lean_closure_set(v___f_3622_, 5, v_inst_3605_);
lean_closure_set(v___f_3622_, 6, v_inst_3611_);
lean_closure_set(v___f_3622_, 7, v_inst_3610_);
lean_closure_set(v___f_3622_, 8, v_inst_3608_);
lean_closure_set(v___f_3622_, 9, v_f_3613_);
lean_closure_set(v___f_3622_, 10, v___f_3621_);
lean_closure_set(v___f_3622_, 11, v___f_3620_);
v___x_3623_ = lean_apply_4(v_toBind_3615_, lean_box(0), lean_box(0), v___x_3618_, v___f_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_3624_, lean_object* v_inst_3625_, lean_object* v_inst_3626_, lean_object* v_inst_3627_, lean_object* v_inst_3628_, lean_object* v_inst_3629_, lean_object* v_inst_3630_, lean_object* v_inst_3631_, lean_object* v_inst_3632_, lean_object* v_f_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_3624_, v_inst_3625_, v_inst_3626_, v_inst_3627_, v_inst_3628_, v_inst_3629_, v_inst_3630_, v_inst_3631_, v_inst_3632_, v_f_3633_);
lean_dec_ref(v_inst_3632_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_3635_, lean_object* v_x_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = lean_apply_1(v_f_3635_, v___y_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_3639_, lean_object* v_inst_3640_, lean_object* v___f_3641_, lean_object* v_hyps_3642_){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v___x_3643_ = lean_unsigned_to_nat(0u);
v___x_3644_ = lean_array_get_size(v_hyps_3642_);
v___x_3645_ = lean_box(0);
v___x_3646_ = lean_nat_dec_lt(v___x_3643_, v___x_3644_);
if (v___x_3646_ == 0)
{
lean_object* v_toPure_3647_; lean_object* v___x_3648_; 
lean_dec_ref(v_hyps_3642_);
lean_dec(v___f_3641_);
lean_dec_ref(v_inst_3640_);
v_toPure_3647_ = lean_ctor_get(v_toApplicative_3639_, 1);
lean_inc(v_toPure_3647_);
lean_dec_ref(v_toApplicative_3639_);
v___x_3648_ = lean_apply_2(v_toPure_3647_, lean_box(0), v___x_3645_);
return v___x_3648_;
}
else
{
uint8_t v___x_3649_; 
v___x_3649_ = lean_nat_dec_le(v___x_3644_, v___x_3644_);
if (v___x_3649_ == 0)
{
if (v___x_3646_ == 0)
{
lean_object* v_toPure_3650_; lean_object* v___x_3651_; 
lean_dec_ref(v_hyps_3642_);
lean_dec(v___f_3641_);
lean_dec_ref(v_inst_3640_);
v_toPure_3650_ = lean_ctor_get(v_toApplicative_3639_, 1);
lean_inc(v_toPure_3650_);
lean_dec_ref(v_toApplicative_3639_);
v___x_3651_ = lean_apply_2(v_toPure_3650_, lean_box(0), v___x_3645_);
return v___x_3651_;
}
else
{
size_t v___x_3652_; size_t v___x_3653_; lean_object* v___x_3654_; 
lean_dec_ref(v_toApplicative_3639_);
v___x_3652_ = ((size_t)0ULL);
v___x_3653_ = lean_usize_of_nat(v___x_3644_);
v___x_3654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3640_, v___f_3641_, v_hyps_3642_, v___x_3652_, v___x_3653_, v___x_3645_);
return v___x_3654_;
}
}
else
{
size_t v___x_3655_; size_t v___x_3656_; lean_object* v___x_3657_; 
lean_dec_ref(v_toApplicative_3639_);
v___x_3655_ = ((size_t)0ULL);
v___x_3656_ = lean_usize_of_nat(v___x_3644_);
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3640_, v___f_3641_, v_hyps_3642_, v___x_3655_, v___x_3656_, v___x_3645_);
return v___x_3657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object* v_inst_3658_, lean_object* v_inst_3659_, lean_object* v_f_3660_){
_start:
{
lean_object* v_toApplicative_3661_; lean_object* v_toBind_3662_; lean_object* v___f_3663_; lean_object* v___f_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v_toApplicative_3661_ = lean_ctor_get(v_inst_3658_, 0);
lean_inc_ref(v_toApplicative_3661_);
v_toBind_3662_ = lean_ctor_get(v_inst_3658_, 1);
lean_inc(v_toBind_3662_);
v___f_3663_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3663_, 0, v_f_3660_);
v___f_3664_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3664_, 0, v_toApplicative_3661_);
lean_closure_set(v___f_3664_, 1, v_inst_3658_);
lean_closure_set(v___f_3664_, 2, v___f_3663_);
v___x_3665_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3666_ = lean_apply_2(v_inst_3659_, lean_box(0), v___x_3665_);
v___x_3667_ = lean_apply_4(v_toBind_3662_, lean_box(0), lean_box(0), v___x_3666_, v___f_3664_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object* v_m_3668_, lean_object* v_inst_3669_, lean_object* v_inst_3670_, lean_object* v_inst_3671_, lean_object* v_f_3672_){
_start:
{
lean_object* v_toApplicative_3673_; lean_object* v_toBind_3674_; lean_object* v___f_3675_; lean_object* v___f_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v_toApplicative_3673_ = lean_ctor_get(v_inst_3669_, 0);
lean_inc_ref(v_toApplicative_3673_);
v_toBind_3674_ = lean_ctor_get(v_inst_3669_, 1);
lean_inc(v_toBind_3674_);
v___f_3675_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3675_, 0, v_f_3672_);
v___f_3676_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3676_, 0, v_toApplicative_3673_);
lean_closure_set(v___f_3676_, 1, v_inst_3669_);
lean_closure_set(v___f_3676_, 2, v___f_3675_);
v___x_3677_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 12, 0);
v___x_3678_ = lean_apply_2(v_inst_3670_, lean_box(0), v___x_3677_);
v___x_3679_ = lean_apply_4(v_toBind_3674_, lean_box(0), lean_box(0), v___x_3678_, v___f_3676_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object* v_m_3680_, lean_object* v_inst_3681_, lean_object* v_inst_3682_, lean_object* v_inst_3683_, lean_object* v_f_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(v_m_3680_, v_inst_3681_, v_inst_3682_, v_inst_3683_, v_f_3684_);
lean_dec_ref(v_inst_3683_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3692_; lean_object* v_env_3693_; lean_object* v___x_3694_; lean_object* v_mctx_3695_; lean_object* v_lctx_3696_; lean_object* v_options_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3692_ = lean_st_ref_get(v___y_3690_);
v_env_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc_ref(v_env_3693_);
lean_dec(v___x_3692_);
v___x_3694_ = lean_st_ref_get(v___y_3688_);
v_mctx_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc_ref(v_mctx_3695_);
lean_dec(v___x_3694_);
v_lctx_3696_ = lean_ctor_get(v___y_3687_, 2);
v_options_3697_ = lean_ctor_get(v___y_3689_, 2);
lean_inc_ref(v_options_3697_);
lean_inc_ref(v_lctx_3696_);
v___x_3698_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3698_, 0, v_env_3693_);
lean_ctor_set(v___x_3698_, 1, v_mctx_3695_);
lean_ctor_set(v___x_3698_, 2, v_lctx_3696_);
lean_ctor_set(v___x_3698_, 3, v_options_3697_);
v___x_3699_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
lean_ctor_set(v___x_3699_, 1, v_msgData_3686_);
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
return v_res_3707_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3708_; double v___x_3709_; 
v___x_3708_ = lean_unsigned_to_nat(0u);
v___x_3709_ = lean_float_of_nat(v___x_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_3713_, lean_object* v_msg_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_ref_3720_; lean_object* v___x_3721_; lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3766_; 
v_ref_3720_ = lean_ctor_get(v___y_3717_, 5);
v___x_3721_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3724_ = v___x_3721_;
v_isShared_3725_ = v_isSharedCheck_3766_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3721_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3766_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3726_; lean_object* v_traceState_3727_; lean_object* v_env_3728_; lean_object* v_nextMacroScope_3729_; lean_object* v_ngen_3730_; lean_object* v_auxDeclNGen_3731_; lean_object* v_cache_3732_; lean_object* v_messages_3733_; lean_object* v_infoState_3734_; lean_object* v_snapshotTasks_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3765_; 
v___x_3726_ = lean_st_ref_take(v___y_3718_);
v_traceState_3727_ = lean_ctor_get(v___x_3726_, 4);
v_env_3728_ = lean_ctor_get(v___x_3726_, 0);
v_nextMacroScope_3729_ = lean_ctor_get(v___x_3726_, 1);
v_ngen_3730_ = lean_ctor_get(v___x_3726_, 2);
v_auxDeclNGen_3731_ = lean_ctor_get(v___x_3726_, 3);
v_cache_3732_ = lean_ctor_get(v___x_3726_, 5);
v_messages_3733_ = lean_ctor_get(v___x_3726_, 6);
v_infoState_3734_ = lean_ctor_get(v___x_3726_, 7);
v_snapshotTasks_3735_ = lean_ctor_get(v___x_3726_, 8);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3737_ = v___x_3726_;
v_isShared_3738_ = v_isSharedCheck_3765_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_snapshotTasks_3735_);
lean_inc(v_infoState_3734_);
lean_inc(v_messages_3733_);
lean_inc(v_cache_3732_);
lean_inc(v_traceState_3727_);
lean_inc(v_auxDeclNGen_3731_);
lean_inc(v_ngen_3730_);
lean_inc(v_nextMacroScope_3729_);
lean_inc(v_env_3728_);
lean_dec(v___x_3726_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3765_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
uint64_t v_tid_3739_; lean_object* v_traces_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3764_; 
v_tid_3739_ = lean_ctor_get_uint64(v_traceState_3727_, sizeof(void*)*1);
v_traces_3740_ = lean_ctor_get(v_traceState_3727_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v_traceState_3727_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3742_ = v_traceState_3727_;
v_isShared_3743_ = v_isSharedCheck_3764_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_traces_3740_);
lean_dec(v_traceState_3727_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3764_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; double v___x_3745_; uint8_t v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3754_; 
v___x_3744_ = lean_box(0);
v___x_3745_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_3746_ = 0;
v___x_3747_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_3748_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3748_, 0, v_cls_3713_);
lean_ctor_set(v___x_3748_, 1, v___x_3744_);
lean_ctor_set(v___x_3748_, 2, v___x_3747_);
lean_ctor_set_float(v___x_3748_, sizeof(void*)*3, v___x_3745_);
lean_ctor_set_float(v___x_3748_, sizeof(void*)*3 + 8, v___x_3745_);
lean_ctor_set_uint8(v___x_3748_, sizeof(void*)*3 + 16, v___x_3746_);
v___x_3749_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_3750_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v_a_3722_);
lean_ctor_set(v___x_3750_, 2, v___x_3749_);
lean_inc(v_ref_3720_);
v___x_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3751_, 0, v_ref_3720_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = l_Lean_PersistentArray_push___redArg(v_traces_3740_, v___x_3751_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v___x_3752_);
v___x_3754_ = v___x_3742_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3752_);
lean_ctor_set_uint64(v_reuseFailAlloc_3763_, sizeof(void*)*1, v_tid_3739_);
v___x_3754_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3756_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 4, v___x_3754_);
v___x_3756_ = v___x_3737_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_env_3728_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_nextMacroScope_3729_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_ngen_3730_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_auxDeclNGen_3731_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3762_, 5, v_cache_3732_);
lean_ctor_set(v_reuseFailAlloc_3762_, 6, v_messages_3733_);
lean_ctor_set(v_reuseFailAlloc_3762_, 7, v_infoState_3734_);
lean_ctor_set(v_reuseFailAlloc_3762_, 8, v_snapshotTasks_3735_);
v___x_3756_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3760_; 
v___x_3757_ = lean_st_ref_set(v___y_3718_, v___x_3756_);
v___x_3758_ = lean_box(0);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v___x_3758_);
v___x_3760_ = v___x_3724_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_3767_, lean_object* v_msg_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_3767_, v_msg_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_3775_, lean_object* v_x_3776_, lean_object* v_x_3777_, lean_object* v_x_3778_){
_start:
{
lean_object* v_ks_3779_; lean_object* v_vs_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3804_; 
v_ks_3779_ = lean_ctor_get(v_x_3775_, 0);
v_vs_3780_ = lean_ctor_get(v_x_3775_, 1);
v_isSharedCheck_3804_ = !lean_is_exclusive(v_x_3775_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3782_ = v_x_3775_;
v_isShared_3783_ = v_isSharedCheck_3804_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_vs_3780_);
lean_inc(v_ks_3779_);
lean_dec(v_x_3775_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3804_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3784_; uint8_t v___x_3785_; 
v___x_3784_ = lean_array_get_size(v_ks_3779_);
v___x_3785_ = lean_nat_dec_lt(v_x_3776_, v___x_3784_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3789_; 
lean_dec(v_x_3776_);
v___x_3786_ = lean_array_push(v_ks_3779_, v_x_3777_);
v___x_3787_ = lean_array_push(v_vs_3780_, v_x_3778_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 1, v___x_3787_);
lean_ctor_set(v___x_3782_, 0, v___x_3786_);
v___x_3789_ = v___x_3782_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3786_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
else
{
lean_object* v_k_x27_3791_; uint8_t v___x_3792_; 
v_k_x27_3791_ = lean_array_fget_borrowed(v_ks_3779_, v_x_3776_);
v___x_3792_ = l_Lean_instBEqMVarId_beq(v_x_3777_, v_k_x27_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3794_; 
if (v_isShared_3783_ == 0)
{
v___x_3794_ = v___x_3782_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_ks_3779_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_vs_3780_);
v___x_3794_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = lean_unsigned_to_nat(1u);
v___x_3796_ = lean_nat_add(v_x_3776_, v___x_3795_);
lean_dec(v_x_3776_);
v_x_3775_ = v___x_3794_;
v_x_3776_ = v___x_3796_;
goto _start;
}
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3802_; 
v___x_3799_ = lean_array_fset(v_ks_3779_, v_x_3776_, v_x_3777_);
v___x_3800_ = lean_array_fset(v_vs_3780_, v_x_3776_, v_x_3778_);
lean_dec(v_x_3776_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 1, v___x_3800_);
lean_ctor_set(v___x_3782_, 0, v___x_3799_);
v___x_3802_ = v___x_3782_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v___x_3800_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_n_3805_, lean_object* v_k_3806_, lean_object* v_v_3807_){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = lean_unsigned_to_nat(0u);
v___x_3809_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_n_3805_, v___x_3808_, v_k_3806_, v_v_3807_);
return v___x_3809_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3811_, size_t v_x_3812_, size_t v_x_3813_, lean_object* v_x_3814_, lean_object* v_x_3815_){
_start:
{
if (lean_obj_tag(v_x_3811_) == 0)
{
lean_object* v_es_3816_; size_t v___x_3817_; size_t v___x_3818_; lean_object* v_j_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v_es_3816_ = lean_ctor_get(v_x_3811_, 0);
v___x_3817_ = ((size_t)31ULL);
v___x_3818_ = lean_usize_land(v_x_3812_, v___x_3817_);
v_j_3819_ = lean_usize_to_nat(v___x_3818_);
v___x_3820_ = lean_array_get_size(v_es_3816_);
v___x_3821_ = lean_nat_dec_lt(v_j_3819_, v___x_3820_);
if (v___x_3821_ == 0)
{
lean_dec(v_j_3819_);
lean_dec(v_x_3815_);
lean_dec(v_x_3814_);
return v_x_3811_;
}
else
{
lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3860_; 
lean_inc_ref(v_es_3816_);
v_isSharedCheck_3860_ = !lean_is_exclusive(v_x_3811_);
if (v_isSharedCheck_3860_ == 0)
{
lean_object* v_unused_3861_; 
v_unused_3861_ = lean_ctor_get(v_x_3811_, 0);
lean_dec(v_unused_3861_);
v___x_3823_ = v_x_3811_;
v_isShared_3824_ = v_isSharedCheck_3860_;
goto v_resetjp_3822_;
}
else
{
lean_dec(v_x_3811_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3860_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v_v_3825_; lean_object* v___x_3826_; lean_object* v_xs_x27_3827_; lean_object* v___y_3829_; 
v_v_3825_ = lean_array_fget(v_es_3816_, v_j_3819_);
v___x_3826_ = lean_box(0);
v_xs_x27_3827_ = lean_array_fset(v_es_3816_, v_j_3819_, v___x_3826_);
switch(lean_obj_tag(v_v_3825_))
{
case 0:
{
lean_object* v_key_3834_; lean_object* v_val_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3845_; 
v_key_3834_ = lean_ctor_get(v_v_3825_, 0);
v_val_3835_ = lean_ctor_get(v_v_3825_, 1);
v_isSharedCheck_3845_ = !lean_is_exclusive(v_v_3825_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3837_ = v_v_3825_;
v_isShared_3838_ = v_isSharedCheck_3845_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_val_3835_);
lean_inc(v_key_3834_);
lean_dec(v_v_3825_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3845_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
uint8_t v___x_3839_; 
v___x_3839_ = l_Lean_instBEqMVarId_beq(v_x_3814_, v_key_3834_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_del_object(v___x_3837_);
v___x_3840_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3834_, v_val_3835_, v_x_3814_, v_x_3815_);
v___x_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
v___y_3829_ = v___x_3841_;
goto v___jp_3828_;
}
else
{
lean_object* v___x_3843_; 
lean_dec(v_val_3835_);
lean_dec(v_key_3834_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 1, v_x_3815_);
lean_ctor_set(v___x_3837_, 0, v_x_3814_);
v___x_3843_ = v___x_3837_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_x_3814_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v_x_3815_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
v___y_3829_ = v___x_3843_;
goto v___jp_3828_;
}
}
}
}
case 1:
{
lean_object* v_node_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3858_; 
v_node_3846_ = lean_ctor_get(v_v_3825_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_v_3825_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3848_ = v_v_3825_;
v_isShared_3849_ = v_isSharedCheck_3858_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_node_3846_);
lean_dec(v_v_3825_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3858_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
size_t v___x_3850_; size_t v___x_3851_; size_t v___x_3852_; size_t v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3856_; 
v___x_3850_ = ((size_t)5ULL);
v___x_3851_ = lean_usize_shift_right(v_x_3812_, v___x_3850_);
v___x_3852_ = ((size_t)1ULL);
v___x_3853_ = lean_usize_add(v_x_3813_, v___x_3852_);
v___x_3854_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_node_3846_, v___x_3851_, v___x_3853_, v_x_3814_, v_x_3815_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 0, v___x_3854_);
v___x_3856_ = v___x_3848_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
v___y_3829_ = v___x_3856_;
goto v___jp_3828_;
}
}
}
default: 
{
lean_object* v___x_3859_; 
v___x_3859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3859_, 0, v_x_3814_);
lean_ctor_set(v___x_3859_, 1, v_x_3815_);
v___y_3829_ = v___x_3859_;
goto v___jp_3828_;
}
}
v___jp_3828_:
{
lean_object* v___x_3830_; lean_object* v___x_3832_; 
v___x_3830_ = lean_array_fset(v_xs_x27_3827_, v_j_3819_, v___y_3829_);
lean_dec(v_j_3819_);
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 0, v___x_3830_);
v___x_3832_ = v___x_3823_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
}
else
{
lean_object* v_ks_3862_; lean_object* v_vs_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3883_; 
v_ks_3862_ = lean_ctor_get(v_x_3811_, 0);
v_vs_3863_ = lean_ctor_get(v_x_3811_, 1);
v_isSharedCheck_3883_ = !lean_is_exclusive(v_x_3811_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3865_ = v_x_3811_;
v_isShared_3866_ = v_isSharedCheck_3883_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_vs_3863_);
lean_inc(v_ks_3862_);
lean_dec(v_x_3811_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3883_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_ks_3862_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_vs_3863_);
v___x_3868_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v_newNode_3869_; uint8_t v___y_3871_; size_t v___x_3877_; uint8_t v___x_3878_; 
v_newNode_3869_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5___redArg(v___x_3868_, v_x_3814_, v_x_3815_);
v___x_3877_ = ((size_t)7ULL);
v___x_3878_ = lean_usize_dec_le(v___x_3877_, v_x_3813_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3879_; lean_object* v___x_3880_; uint8_t v___x_3881_; 
v___x_3879_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3869_);
v___x_3880_ = lean_unsigned_to_nat(4u);
v___x_3881_ = lean_nat_dec_lt(v___x_3879_, v___x_3880_);
lean_dec(v___x_3879_);
v___y_3871_ = v___x_3881_;
goto v___jp_3870_;
}
else
{
v___y_3871_ = v___x_3878_;
goto v___jp_3870_;
}
v___jp_3870_:
{
if (v___y_3871_ == 0)
{
lean_object* v_ks_3872_; lean_object* v_vs_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_ks_3872_ = lean_ctor_get(v_newNode_3869_, 0);
lean_inc_ref(v_ks_3872_);
v_vs_3873_ = lean_ctor_get(v_newNode_3869_, 1);
lean_inc_ref(v_vs_3873_);
lean_dec_ref(v_newNode_3869_);
v___x_3874_ = lean_unsigned_to_nat(0u);
v___x_3875_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_3876_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(v_x_3813_, v_ks_3872_, v_vs_3873_, v___x_3874_, v___x_3875_);
lean_dec_ref(v_vs_3873_);
lean_dec_ref(v_ks_3872_);
return v___x_3876_;
}
else
{
return v_newNode_3869_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(size_t v_depth_3884_, lean_object* v_keys_3885_, lean_object* v_vals_3886_, lean_object* v_i_3887_, lean_object* v_entries_3888_){
_start:
{
lean_object* v___x_3889_; uint8_t v___x_3890_; 
v___x_3889_ = lean_array_get_size(v_keys_3885_);
v___x_3890_ = lean_nat_dec_lt(v_i_3887_, v___x_3889_);
if (v___x_3890_ == 0)
{
lean_dec(v_i_3887_);
return v_entries_3888_;
}
else
{
lean_object* v_k_3891_; lean_object* v_v_3892_; uint64_t v___x_3893_; size_t v_h_3894_; size_t v___x_3895_; lean_object* v___x_3896_; size_t v___x_3897_; size_t v___x_3898_; size_t v___x_3899_; size_t v_h_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_k_3891_ = lean_array_fget_borrowed(v_keys_3885_, v_i_3887_);
v_v_3892_ = lean_array_fget_borrowed(v_vals_3886_, v_i_3887_);
v___x_3893_ = l_Lean_instHashableMVarId_hash(v_k_3891_);
v_h_3894_ = lean_uint64_to_usize(v___x_3893_);
v___x_3895_ = ((size_t)5ULL);
v___x_3896_ = lean_unsigned_to_nat(1u);
v___x_3897_ = ((size_t)1ULL);
v___x_3898_ = lean_usize_sub(v_depth_3884_, v___x_3897_);
v___x_3899_ = lean_usize_mul(v___x_3895_, v___x_3898_);
v_h_3900_ = lean_usize_shift_right(v_h_3894_, v___x_3899_);
v___x_3901_ = lean_nat_add(v_i_3887_, v___x_3896_);
lean_dec(v_i_3887_);
lean_inc(v_v_3892_);
lean_inc(v_k_3891_);
v___x_3902_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_entries_3888_, v_h_3900_, v_depth_3884_, v_k_3891_, v_v_3892_);
v_i_3887_ = v___x_3901_;
v_entries_3888_ = v___x_3902_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_3904_, lean_object* v_keys_3905_, lean_object* v_vals_3906_, lean_object* v_i_3907_, lean_object* v_entries_3908_){
_start:
{
size_t v_depth_boxed_3909_; lean_object* v_res_3910_; 
v_depth_boxed_3909_ = lean_unbox_usize(v_depth_3904_);
lean_dec(v_depth_3904_);
v_res_3910_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_boxed_3909_, v_keys_3905_, v_vals_3906_, v_i_3907_, v_entries_3908_);
lean_dec_ref(v_vals_3906_);
lean_dec_ref(v_keys_3905_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_x_3911_, lean_object* v_x_3912_, lean_object* v_x_3913_, lean_object* v_x_3914_, lean_object* v_x_3915_){
_start:
{
size_t v_x_38046__boxed_3916_; size_t v_x_38047__boxed_3917_; lean_object* v_res_3918_; 
v_x_38046__boxed_3916_ = lean_unbox_usize(v_x_3912_);
lean_dec(v_x_3912_);
v_x_38047__boxed_3917_ = lean_unbox_usize(v_x_3913_);
lean_dec(v_x_3913_);
v_res_3918_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_x_3911_, v_x_38046__boxed_3916_, v_x_38047__boxed_3917_, v_x_3914_, v_x_3915_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(lean_object* v_x_3919_, lean_object* v_x_3920_, lean_object* v_x_3921_){
_start:
{
uint64_t v___x_3922_; size_t v___x_3923_; size_t v___x_3924_; lean_object* v___x_3925_; 
v___x_3922_ = l_Lean_instHashableMVarId_hash(v_x_3920_);
v___x_3923_ = lean_uint64_to_usize(v___x_3922_);
v___x_3924_ = ((size_t)1ULL);
v___x_3925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_x_3919_, v___x_3923_, v___x_3924_, v_x_3920_, v_x_3921_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object* v_mvarId_3926_, lean_object* v_val_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v___x_3930_; lean_object* v_mctx_3931_; lean_object* v_cache_3932_; lean_object* v_zetaDeltaFVarIds_3933_; lean_object* v_postponed_3934_; lean_object* v_diag_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3963_; 
v___x_3930_ = lean_st_ref_take(v___y_3928_);
v_mctx_3931_ = lean_ctor_get(v___x_3930_, 0);
v_cache_3932_ = lean_ctor_get(v___x_3930_, 1);
v_zetaDeltaFVarIds_3933_ = lean_ctor_get(v___x_3930_, 2);
v_postponed_3934_ = lean_ctor_get(v___x_3930_, 3);
v_diag_3935_ = lean_ctor_get(v___x_3930_, 4);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3937_ = v___x_3930_;
v_isShared_3938_ = v_isSharedCheck_3963_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_diag_3935_);
lean_inc(v_postponed_3934_);
lean_inc(v_zetaDeltaFVarIds_3933_);
lean_inc(v_cache_3932_);
lean_inc(v_mctx_3931_);
lean_dec(v___x_3930_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3963_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v_depth_3939_; lean_object* v_levelAssignDepth_3940_; lean_object* v_lmvarCounter_3941_; lean_object* v_mvarCounter_3942_; lean_object* v_lDecls_3943_; lean_object* v_decls_3944_; lean_object* v_userNames_3945_; lean_object* v_lAssignment_3946_; lean_object* v_eAssignment_3947_; lean_object* v_dAssignment_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3962_; 
v_depth_3939_ = lean_ctor_get(v_mctx_3931_, 0);
v_levelAssignDepth_3940_ = lean_ctor_get(v_mctx_3931_, 1);
v_lmvarCounter_3941_ = lean_ctor_get(v_mctx_3931_, 2);
v_mvarCounter_3942_ = lean_ctor_get(v_mctx_3931_, 3);
v_lDecls_3943_ = lean_ctor_get(v_mctx_3931_, 4);
v_decls_3944_ = lean_ctor_get(v_mctx_3931_, 5);
v_userNames_3945_ = lean_ctor_get(v_mctx_3931_, 6);
v_lAssignment_3946_ = lean_ctor_get(v_mctx_3931_, 7);
v_eAssignment_3947_ = lean_ctor_get(v_mctx_3931_, 8);
v_dAssignment_3948_ = lean_ctor_get(v_mctx_3931_, 9);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_mctx_3931_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3950_ = v_mctx_3931_;
v_isShared_3951_ = v_isSharedCheck_3962_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_dAssignment_3948_);
lean_inc(v_eAssignment_3947_);
lean_inc(v_lAssignment_3946_);
lean_inc(v_userNames_3945_);
lean_inc(v_decls_3944_);
lean_inc(v_lDecls_3943_);
lean_inc(v_mvarCounter_3942_);
lean_inc(v_lmvarCounter_3941_);
lean_inc(v_levelAssignDepth_3940_);
lean_inc(v_depth_3939_);
lean_dec(v_mctx_3931_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3962_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3952_; lean_object* v___x_3954_; 
v___x_3952_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(v_eAssignment_3947_, v_mvarId_3926_, v_val_3927_);
if (v_isShared_3951_ == 0)
{
lean_ctor_set(v___x_3950_, 8, v___x_3952_);
v___x_3954_ = v___x_3950_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_depth_3939_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_levelAssignDepth_3940_);
lean_ctor_set(v_reuseFailAlloc_3961_, 2, v_lmvarCounter_3941_);
lean_ctor_set(v_reuseFailAlloc_3961_, 3, v_mvarCounter_3942_);
lean_ctor_set(v_reuseFailAlloc_3961_, 4, v_lDecls_3943_);
lean_ctor_set(v_reuseFailAlloc_3961_, 5, v_decls_3944_);
lean_ctor_set(v_reuseFailAlloc_3961_, 6, v_userNames_3945_);
lean_ctor_set(v_reuseFailAlloc_3961_, 7, v_lAssignment_3946_);
lean_ctor_set(v_reuseFailAlloc_3961_, 8, v___x_3952_);
lean_ctor_set(v_reuseFailAlloc_3961_, 9, v_dAssignment_3948_);
v___x_3954_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_object* v___x_3956_; 
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v___x_3954_);
v___x_3956_ = v___x_3937_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_3960_, 1, v_cache_3932_);
lean_ctor_set(v_reuseFailAlloc_3960_, 2, v_zetaDeltaFVarIds_3933_);
lean_ctor_set(v_reuseFailAlloc_3960_, 3, v_postponed_3934_);
lean_ctor_set(v_reuseFailAlloc_3960_, 4, v_diag_3935_);
v___x_3956_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3957_ = lean_st_ref_set(v___y_3928_, v___x_3956_);
v___x_3958_ = lean_box(0);
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
return v___x_3959_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object* v_mvarId_3964_, lean_object* v_val_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_mvarId_3964_, v_val_3965_, v___y_3966_);
lean_dec(v___y_3966_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(uint8_t v___x_3969_, lean_object* v___f_3970_, lean_object* v_____r_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v___x_3985_; lean_object* v_rewriteSimpCache_3986_; lean_object* v_rewriteDSimpCache_3987_; lean_object* v_acCache_3988_; lean_object* v_typeAnalysis_3989_; lean_object* v_target_3990_; lean_object* v_hypotheses_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4001_; 
v___x_3985_ = lean_st_ref_take(v___y_3974_);
v_rewriteSimpCache_3986_ = lean_ctor_get(v___x_3985_, 0);
v_rewriteDSimpCache_3987_ = lean_ctor_get(v___x_3985_, 1);
v_acCache_3988_ = lean_ctor_get(v___x_3985_, 2);
v_typeAnalysis_3989_ = lean_ctor_get(v___x_3985_, 3);
v_target_3990_ = lean_ctor_get(v___x_3985_, 4);
v_hypotheses_3991_ = lean_ctor_get(v___x_3985_, 5);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3993_ = v___x_3985_;
v_isShared_3994_ = v_isSharedCheck_4001_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_hypotheses_3991_);
lean_inc(v_target_3990_);
lean_inc(v_typeAnalysis_3989_);
lean_inc(v_acCache_3988_);
lean_inc(v_rewriteDSimpCache_3987_);
lean_inc(v_rewriteSimpCache_3986_);
lean_dec(v___x_3985_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4001_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_rewriteSimpCache_3986_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v_rewriteDSimpCache_3987_);
lean_ctor_set(v_reuseFailAlloc_4000_, 2, v_acCache_3988_);
lean_ctor_set(v_reuseFailAlloc_4000_, 3, v_typeAnalysis_3989_);
lean_ctor_set(v_reuseFailAlloc_4000_, 4, v_target_3990_);
lean_ctor_set(v_reuseFailAlloc_4000_, 5, v_hypotheses_3991_);
v___x_3996_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
lean_ctor_set_uint8(v___x_3996_, sizeof(void*)*6, v___x_3969_);
v___x_3997_ = lean_st_ref_set(v___y_3974_, v___x_3996_);
v___x_3998_ = lean_box(0);
lean_inc(v___y_3983_);
lean_inc_ref(v___y_3982_);
lean_inc(v___y_3981_);
lean_inc_ref(v___y_3980_);
lean_inc(v___y_3979_);
lean_inc_ref(v___y_3978_);
lean_inc(v___y_3977_);
lean_inc_ref(v___y_3976_);
lean_inc(v___y_3975_);
lean_inc(v___y_3974_);
lean_inc_ref(v___y_3973_);
lean_inc(v___y_3972_);
v___x_3999_ = lean_apply_14(v___f_3970_, v___x_3998_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, lean_box(0));
return v___x_3999_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1___boxed(lean_object* v___x_4002_, lean_object* v___f_4003_, lean_object* v_____r_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
uint8_t v___x_38259__boxed_4018_; lean_object* v_res_4019_; 
v___x_38259__boxed_4018_ = lean_unbox(v___x_4002_);
v_res_4019_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_38259__boxed_4018_, v___f_4003_, v_____r_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(lean_object* v_snd_4020_, lean_object* v_a_4021_, lean_object* v___x_4022_, lean_object* v_____r_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4037_ = lean_array_push(v_snd_4020_, v_a_4021_);
v___x_4038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4022_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
v___x_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
v___x_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4039_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_4041_ = _args[0];
lean_object* v_a_4042_ = _args[1];
lean_object* v___x_4043_ = _args[2];
lean_object* v_____r_4044_ = _args[3];
lean_object* v___y_4045_ = _args[4];
lean_object* v___y_4046_ = _args[5];
lean_object* v___y_4047_ = _args[6];
lean_object* v___y_4048_ = _args[7];
lean_object* v___y_4049_ = _args[8];
lean_object* v___y_4050_ = _args[9];
lean_object* v___y_4051_ = _args[10];
lean_object* v___y_4052_ = _args[11];
lean_object* v___y_4053_ = _args[12];
lean_object* v___y_4054_ = _args[13];
lean_object* v___y_4055_ = _args[14];
lean_object* v___y_4056_ = _args[15];
lean_object* v___y_4057_ = _args[16];
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(v_snd_4041_, v_a_4042_, v___x_4043_, v_____r_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(lean_object* v_upperBound_4059_, lean_object* v___x_4060_, lean_object* v_methods_4061_, lean_object* v_config_4062_, lean_object* v_a_4063_, lean_object* v_b_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v___y_4079_; uint8_t v___x_4101_; 
v___x_4101_ = lean_nat_dec_lt(v_a_4063_, v_upperBound_4059_);
if (v___x_4101_ == 0)
{
lean_object* v___x_4102_; 
lean_dec(v_a_4063_);
lean_dec_ref(v_config_4062_);
lean_dec_ref(v_methods_4061_);
v___x_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4102_, 0, v_b_4064_);
return v___x_4102_;
}
else
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v_type_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4103_ = lean_st_ref_take(v___y_4065_);
v___x_4104_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_4105_ = lean_st_ref_set(v___y_4065_, v___x_4104_);
v___x_4106_ = lean_array_fget_borrowed(v___x_4060_, v_a_4063_);
v_type_4107_ = lean_ctor_get(v___x_4106_, 1);
v___x_4108_ = lean_unsigned_to_nat(0u);
v___x_4109_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
lean_ctor_set(v___x_4109_, 1, v___x_4103_);
lean_ctor_set(v___x_4109_, 2, v___x_4104_);
lean_ctor_set(v___x_4109_, 3, v___x_4104_);
lean_inc_ref(v_type_4107_);
v___x_4110_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_4110_, 0, v_type_4107_);
lean_inc_ref(v_config_4062_);
lean_inc_ref(v_methods_4061_);
v___x_4111_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_4110_, v_methods_4061_, v_config_4062_, v___x_4109_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v_snd_4113_; lean_object* v_fst_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4197_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v_snd_4113_ = lean_ctor_get(v_a_4112_, 1);
v_fst_4114_ = lean_ctor_get(v_a_4112_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v_a_4112_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4116_ = v_a_4112_;
v_isShared_4117_ = v_isSharedCheck_4197_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_snd_4113_);
lean_inc(v_fst_4114_);
lean_dec(v_a_4112_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4197_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v_persistentCache_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v_persistentCache_4118_ = lean_ctor_get(v_snd_4113_, 1);
lean_inc_ref(v_persistentCache_4118_);
lean_dec(v_snd_4113_);
v___x_4119_ = lean_st_ref_set(v___y_4065_, v_persistentCache_4118_);
lean_inc(v___x_4106_);
v___x_4120_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_4106_, v_fst_4114_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; lean_object* v_snd_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4187_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref_known(v___x_4120_, 1);
v_snd_4122_ = lean_ctor_get(v_b_4064_, 1);
v_isSharedCheck_4187_ = !lean_is_exclusive(v_b_4064_);
if (v_isSharedCheck_4187_ == 0)
{
lean_object* v_unused_4188_; 
v_unused_4188_ = lean_ctor_get(v_b_4064_, 0);
lean_dec(v_unused_4188_);
v___x_4124_ = v_b_4064_;
v_isShared_4125_ = v_isSharedCheck_4187_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_snd_4122_);
lean_dec(v_b_4064_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4187_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v_type_4126_; lean_object* v_value_4127_; uint8_t v___x_4128_; 
v_type_4126_ = lean_ctor_get(v_a_4121_, 1);
v_value_4127_ = lean_ctor_get(v_a_4121_, 2);
lean_inc_ref(v_type_4126_);
v___x_4128_ = l_Lean_Expr_isFalse(v_type_4126_);
if (v___x_4128_ == 0)
{
lean_object* v___x_4129_; lean_object* v___f_4130_; uint8_t v___x_4159_; 
lean_del_object(v___x_4124_);
v___x_4129_ = lean_box(0);
lean_inc(v_a_4121_);
lean_inc(v_snd_4122_);
v___f_4130_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_4130_, 0, v_snd_4122_);
lean_closure_set(v___f_4130_, 1, v_a_4121_);
lean_closure_set(v___f_4130_, 2, v___x_4129_);
v___x_4159_ = lean_expr_eqv(v_type_4107_, v_type_4126_);
if (v___x_4159_ == 0)
{
lean_inc_ref(v_type_4126_);
lean_dec(v_snd_4122_);
lean_dec(v_a_4121_);
goto v___jp_4134_;
}
else
{
if (v___x_4128_ == 0)
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_dec_ref(v___f_4130_);
lean_del_object(v___x_4116_);
v___x_4160_ = lean_box(0);
v___x_4161_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(v_snd_4122_, v_a_4121_, v___x_4129_, v___x_4160_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
v___y_4079_ = v___x_4161_;
goto v___jp_4078_;
}
else
{
lean_inc_ref(v_type_4126_);
lean_dec(v_snd_4122_);
lean_dec(v_a_4121_);
goto v___jp_4134_;
}
}
v___jp_4131_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = lean_box(0);
v___x_4133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_4101_, v___f_4130_, v___x_4132_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
v___y_4079_ = v___x_4133_;
goto v___jp_4078_;
}
v___jp_4134_:
{
lean_object* v_options_4135_; uint8_t v_hasTrace_4136_; 
v_options_4135_ = lean_ctor_get(v___y_4075_, 2);
v_hasTrace_4136_ = lean_ctor_get_uint8(v_options_4135_, sizeof(void*)*1);
if (v_hasTrace_4136_ == 0)
{
lean_dec_ref(v_type_4126_);
lean_del_object(v___x_4116_);
goto v___jp_4131_;
}
else
{
lean_object* v_inheritedTraceOptions_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; uint8_t v___x_4140_; 
v_inheritedTraceOptions_4137_ = lean_ctor_get(v___y_4075_, 13);
v___x_4138_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
v___x_4139_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___x_4140_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4137_, v_options_4135_, v___x_4139_);
if (v___x_4140_ == 0)
{
lean_dec_ref(v_type_4126_);
lean_del_object(v___x_4116_);
goto v___jp_4131_;
}
else
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4144_; 
lean_inc_ref(v_type_4107_);
v___x_4141_ = l_Lean_MessageData_ofExpr(v_type_4107_);
v___x_4142_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_4117_ == 0)
{
lean_ctor_set_tag(v___x_4116_, 7);
lean_ctor_set(v___x_4116_, 1, v___x_4142_);
lean_ctor_set(v___x_4116_, 0, v___x_4141_);
v___x_4144_ = v___x_4116_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4141_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v___x_4142_);
v___x_4144_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4145_ = l_Lean_MessageData_ofExpr(v_type_4126_);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4144_);
lean_ctor_set(v___x_4146_, 1, v___x_4145_);
v___x_4147_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v___x_4138_, v___x_4146_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; lean_object* v___x_4149_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4147_, 1);
v___x_4149_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_4101_, v___f_4130_, v_a_4148_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
v___y_4079_ = v___x_4149_;
goto v___jp_4078_;
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec_ref(v___f_4130_);
lean_dec(v_a_4063_);
lean_dec_ref(v_config_4062_);
lean_dec_ref(v_methods_4061_);
v_a_4150_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4147_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4147_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
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
lean_object* v___x_4162_; lean_object* v_target_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
lean_inc_ref(v_value_4127_);
lean_dec(v_a_4121_);
lean_del_object(v___x_4116_);
lean_dec(v_a_4063_);
lean_dec_ref(v_config_4062_);
lean_dec_ref(v_methods_4061_);
v___x_4162_ = lean_st_ref_get(v___y_4067_);
v_target_4163_ = lean_ctor_get(v___x_4162_, 4);
lean_inc_ref(v_target_4163_);
lean_dec(v___x_4162_);
v___x_4164_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_4163_);
lean_dec_ref(v_target_4163_);
v___x_4165_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v___x_4164_, v_value_4127_, v___y_4074_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4177_; 
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4177_ == 0)
{
lean_object* v_unused_4178_; 
v_unused_4178_ = lean_ctor_get(v___x_4165_, 0);
lean_dec(v_unused_4178_);
v___x_4167_ = v___x_4165_;
v_isShared_4168_ = v_isSharedCheck_4177_;
goto v_resetjp_4166_;
}
else
{
lean_dec(v___x_4165_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4177_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4172_; 
v___x_4169_ = lean_box(v___x_4128_);
v___x_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 0, v___x_4170_);
v___x_4172_ = v___x_4124_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4170_);
lean_ctor_set(v_reuseFailAlloc_4176_, 1, v_snd_4122_);
v___x_4172_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4174_; 
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v___x_4172_);
v___x_4174_ = v___x_4167_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4172_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_del_object(v___x_4124_);
lean_dec(v_snd_4122_);
v_a_4179_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4165_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4165_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
}
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
lean_del_object(v___x_4116_);
lean_dec_ref(v_b_4064_);
lean_dec(v_a_4063_);
lean_dec_ref(v_config_4062_);
lean_dec_ref(v_methods_4061_);
v_a_4189_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4120_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4120_);
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
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec_ref(v_b_4064_);
lean_dec(v_a_4063_);
lean_dec_ref(v_config_4062_);
lean_dec_ref(v_methods_4061_);
v_a_4198_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4111_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4111_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
v___jp_4078_:
{
if (lean_obj_tag(v___y_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4092_; 
v_a_4080_ = lean_ctor_get(v___y_4079_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___y_4079_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4082_ = v___y_4079_;
v_isShared_4083_ = v_isSharedCheck_4092_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___y_4079_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4092_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
if (lean_obj_tag(v_a_4080_) == 0)
{
lean_object* v_a_4084_; lean_object* v___x_4086_; 
lean_dec(v_a_4063_);
lean_dec_ref(v_config_4062_);
lean_dec_ref(v_methods_4061_);
v_a_4084_ = lean_ctor_get(v_a_4080_, 0);
lean_inc(v_a_4084_);
lean_dec_ref_known(v_a_4080_, 1);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 0, v_a_4084_);
v___x_4086_ = v___x_4082_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4084_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
else
{
lean_object* v_a_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
lean_del_object(v___x_4082_);
v_a_4088_ = lean_ctor_get(v_a_4080_, 0);
lean_inc(v_a_4088_);
lean_dec_ref_known(v_a_4080_, 1);
v___x_4089_ = lean_unsigned_to_nat(1u);
v___x_4090_ = lean_nat_add(v_a_4063_, v___x_4089_);
lean_dec(v_a_4063_);
v_a_4063_ = v___x_4090_;
v_b_4064_ = v_a_4088_;
goto _start;
}
}
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
lean_dec(v_a_4063_);
lean_dec_ref(v_config_4062_);
lean_dec_ref(v_methods_4061_);
v_a_4093_ = lean_ctor_get(v___y_4079_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___y_4079_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___y_4079_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___y_4079_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_4206_ = _args[0];
lean_object* v___x_4207_ = _args[1];
lean_object* v_methods_4208_ = _args[2];
lean_object* v_config_4209_ = _args[3];
lean_object* v_a_4210_ = _args[4];
lean_object* v_b_4211_ = _args[5];
lean_object* v___y_4212_ = _args[6];
lean_object* v___y_4213_ = _args[7];
lean_object* v___y_4214_ = _args[8];
lean_object* v___y_4215_ = _args[9];
lean_object* v___y_4216_ = _args[10];
lean_object* v___y_4217_ = _args[11];
lean_object* v___y_4218_ = _args[12];
lean_object* v___y_4219_ = _args[13];
lean_object* v___y_4220_ = _args[14];
lean_object* v___y_4221_ = _args[15];
lean_object* v___y_4222_ = _args[16];
lean_object* v___y_4223_ = _args[17];
lean_object* v___y_4224_ = _args[18];
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(v_upperBound_4206_, v___x_4207_, v_methods_4208_, v_config_4209_, v_a_4210_, v_b_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___x_4207_);
lean_dec(v_upperBound_4206_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object* v_methods_4226_, lean_object* v_config_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v___x_4241_; lean_object* v_hypotheses_4242_; lean_object* v___x_4243_; lean_object* v_newHyps_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4241_ = lean_st_ref_get(v_a_4230_);
v_hypotheses_4242_ = lean_ctor_get(v___x_4241_, 5);
lean_inc_ref(v_hypotheses_4242_);
lean_dec(v___x_4241_);
v___x_4243_ = lean_array_get_size(v_hypotheses_4242_);
v_newHyps_4244_ = lean_mk_empty_array_with_capacity(v___x_4243_);
v___x_4245_ = lean_unsigned_to_nat(0u);
v___x_4246_ = lean_box(0);
v___x_4247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4246_);
lean_ctor_set(v___x_4247_, 1, v_newHyps_4244_);
v___x_4248_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(v___x_4243_, v_hypotheses_4242_, v_methods_4226_, v_config_4227_, v___x_4245_, v___x_4247_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
lean_dec_ref(v_hypotheses_4242_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4280_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4251_ = v___x_4248_;
v_isShared_4252_ = v_isSharedCheck_4280_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4248_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4280_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v_fst_4253_; 
v_fst_4253_ = lean_ctor_get(v_a_4249_, 0);
if (lean_obj_tag(v_fst_4253_) == 0)
{
lean_object* v_snd_4254_; lean_object* v___x_4255_; lean_object* v_rewriteSimpCache_4256_; lean_object* v_rewriteDSimpCache_4257_; lean_object* v_acCache_4258_; lean_object* v_typeAnalysis_4259_; lean_object* v_target_4260_; uint8_t v_didChange_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4274_; 
v_snd_4254_ = lean_ctor_get(v_a_4249_, 1);
lean_inc(v_snd_4254_);
lean_dec(v_a_4249_);
v___x_4255_ = lean_st_ref_take(v_a_4230_);
v_rewriteSimpCache_4256_ = lean_ctor_get(v___x_4255_, 0);
v_rewriteDSimpCache_4257_ = lean_ctor_get(v___x_4255_, 1);
v_acCache_4258_ = lean_ctor_get(v___x_4255_, 2);
v_typeAnalysis_4259_ = lean_ctor_get(v___x_4255_, 3);
v_target_4260_ = lean_ctor_get(v___x_4255_, 4);
v_didChange_4261_ = lean_ctor_get_uint8(v___x_4255_, sizeof(void*)*6);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4274_ == 0)
{
lean_object* v_unused_4275_; 
v_unused_4275_ = lean_ctor_get(v___x_4255_, 5);
lean_dec(v_unused_4275_);
v___x_4263_ = v___x_4255_;
v_isShared_4264_ = v_isSharedCheck_4274_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_target_4260_);
lean_inc(v_typeAnalysis_4259_);
lean_inc(v_acCache_4258_);
lean_inc(v_rewriteDSimpCache_4257_);
lean_inc(v_rewriteSimpCache_4256_);
lean_dec(v___x_4255_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4274_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 5, v_snd_4254_);
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_rewriteSimpCache_4256_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v_rewriteDSimpCache_4257_);
lean_ctor_set(v_reuseFailAlloc_4273_, 2, v_acCache_4258_);
lean_ctor_set(v_reuseFailAlloc_4273_, 3, v_typeAnalysis_4259_);
lean_ctor_set(v_reuseFailAlloc_4273_, 4, v_target_4260_);
lean_ctor_set(v_reuseFailAlloc_4273_, 5, v_snd_4254_);
lean_ctor_set_uint8(v_reuseFailAlloc_4273_, sizeof(void*)*6, v_didChange_4261_);
v___x_4266_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
lean_object* v___x_4267_; uint8_t v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4271_; 
v___x_4267_ = lean_st_ref_set(v_a_4230_, v___x_4266_);
v___x_4268_ = 0;
v___x_4269_ = lean_box(v___x_4268_);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 0, v___x_4269_);
v___x_4271_ = v___x_4251_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4269_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
else
{
lean_object* v_val_4276_; lean_object* v___x_4278_; 
lean_inc_ref(v_fst_4253_);
lean_dec(v_a_4249_);
v_val_4276_ = lean_ctor_get(v_fst_4253_, 0);
lean_inc(v_val_4276_);
lean_dec_ref_known(v_fst_4253_, 1);
if (v_isShared_4252_ == 0)
{
lean_ctor_set(v___x_4251_, 0, v_val_4276_);
v___x_4278_ = v___x_4251_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_val_4276_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
v_a_4281_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4248_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4248_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object* v_methods_4289_, lean_object* v_config_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_4289_, v_config_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
lean_dec(v_a_4300_);
lean_dec_ref(v_a_4299_);
lean_dec(v_a_4298_);
lean_dec_ref(v_a_4297_);
lean_dec(v_a_4296_);
lean_dec_ref(v_a_4295_);
lean_dec(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec_ref(v_a_4292_);
lean_dec(v_a_4291_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object* v_cls_4305_, lean_object* v_msg_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_4305_, v_msg_4306_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object* v_cls_4321_, lean_object* v_msg_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(v_cls_4321_, v_msg_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
lean_dec(v___y_4332_);
lean_dec_ref(v___y_4331_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec(v___y_4323_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object* v_mvarId_4337_, lean_object* v_val_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
lean_object* v___x_4352_; 
v___x_4352_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_mvarId_4337_, v_val_4338_, v___y_4348_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object* v_mvarId_4353_, lean_object* v_val_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(v_mvarId_4353_, v_val_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec(v___y_4362_);
lean_dec_ref(v___y_4361_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2(lean_object* v_upperBound_4369_, lean_object* v___x_4370_, lean_object* v_methods_4371_, lean_object* v_config_4372_, lean_object* v_inst_4373_, lean_object* v_R_4374_, lean_object* v_a_4375_, lean_object* v_b_4376_, lean_object* v_c_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(v_upperBound_4369_, v___x_4370_, v_methods_4371_, v_config_4372_, v_a_4375_, v_b_4376_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_4392_ = _args[0];
lean_object* v___x_4393_ = _args[1];
lean_object* v_methods_4394_ = _args[2];
lean_object* v_config_4395_ = _args[3];
lean_object* v_inst_4396_ = _args[4];
lean_object* v_R_4397_ = _args[5];
lean_object* v_a_4398_ = _args[6];
lean_object* v_b_4399_ = _args[7];
lean_object* v_c_4400_ = _args[8];
lean_object* v___y_4401_ = _args[9];
lean_object* v___y_4402_ = _args[10];
lean_object* v___y_4403_ = _args[11];
lean_object* v___y_4404_ = _args[12];
lean_object* v___y_4405_ = _args[13];
lean_object* v___y_4406_ = _args[14];
lean_object* v___y_4407_ = _args[15];
lean_object* v___y_4408_ = _args[16];
lean_object* v___y_4409_ = _args[17];
lean_object* v___y_4410_ = _args[18];
lean_object* v___y_4411_ = _args[19];
lean_object* v___y_4412_ = _args[20];
lean_object* v___y_4413_ = _args[21];
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2(v_upperBound_4392_, v___x_4393_, v_methods_4394_, v_config_4395_, v_inst_4396_, v_R_4397_, v_a_4398_, v_b_4399_, v_c_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___x_4393_);
lean_dec(v_upperBound_4392_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2(lean_object* v_00_u03b2_4415_, lean_object* v_x_4416_, lean_object* v_x_4417_, lean_object* v_x_4418_){
_start:
{
lean_object* v___x_4419_; 
v___x_4419_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(v_x_4416_, v_x_4417_, v_x_4418_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4420_, lean_object* v_x_4421_, size_t v_x_4422_, size_t v_x_4423_, lean_object* v_x_4424_, lean_object* v_x_4425_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_x_4421_, v_x_4422_, v_x_4423_, v_x_4424_, v_x_4425_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4427_, lean_object* v_x_4428_, lean_object* v_x_4429_, lean_object* v_x_4430_, lean_object* v_x_4431_, lean_object* v_x_4432_){
_start:
{
size_t v_x_38915__boxed_4433_; size_t v_x_38916__boxed_4434_; lean_object* v_res_4435_; 
v_x_38915__boxed_4433_ = lean_unbox_usize(v_x_4429_);
lean_dec(v_x_4429_);
v_x_38916__boxed_4434_ = lean_unbox_usize(v_x_4430_);
lean_dec(v_x_4430_);
v_res_4435_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3(v_00_u03b2_4427_, v_x_4428_, v_x_38915__boxed_4433_, v_x_38916__boxed_4434_, v_x_4431_, v_x_4432_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4436_, lean_object* v_n_4437_, lean_object* v_k_4438_, lean_object* v_v_4439_){
_start:
{
lean_object* v___x_4440_; 
v___x_4440_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5___redArg(v_n_4437_, v_k_4438_, v_v_4439_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_4441_, size_t v_depth_4442_, lean_object* v_keys_4443_, lean_object* v_vals_4444_, lean_object* v_heq_4445_, lean_object* v_i_4446_, lean_object* v_entries_4447_){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_4442_, v_keys_4443_, v_vals_4444_, v_i_4446_, v_entries_4447_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4449_, lean_object* v_depth_4450_, lean_object* v_keys_4451_, lean_object* v_vals_4452_, lean_object* v_heq_4453_, lean_object* v_i_4454_, lean_object* v_entries_4455_){
_start:
{
size_t v_depth_boxed_4456_; lean_object* v_res_4457_; 
v_depth_boxed_4456_ = lean_unbox_usize(v_depth_4450_);
lean_dec(v_depth_4450_);
v_res_4457_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6(v_00_u03b2_4449_, v_depth_boxed_4456_, v_keys_4451_, v_vals_4452_, v_heq_4453_, v_i_4454_, v_entries_4455_);
lean_dec_ref(v_vals_4452_);
lean_dec_ref(v_keys_4451_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_4458_, lean_object* v_x_4459_, lean_object* v_x_4460_, lean_object* v_x_4461_, lean_object* v_x_4462_){
_start:
{
lean_object* v___x_4463_; 
v___x_4463_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_x_4459_, v_x_4460_, v_x_4461_, v_x_4462_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object* v_methods_4464_, lean_object* v_config_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_){
_start:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4478_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_4479_ = lean_st_mk_ref(v___x_4478_);
v___x_4480_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_4464_, v_config_4465_, v___x_4479_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4489_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4483_ = v___x_4480_;
v_isShared_4484_ = v_isSharedCheck_4489_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4480_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4489_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4485_; lean_object* v___x_4487_; 
v___x_4485_ = lean_st_ref_get(v___x_4479_);
lean_dec(v___x_4479_);
lean_dec(v___x_4485_);
if (v_isShared_4484_ == 0)
{
v___x_4487_ = v___x_4483_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4481_);
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
lean_dec(v___x_4479_);
return v___x_4480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object* v_methods_4490_, lean_object* v_config_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(v_methods_4490_, v_config_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
lean_dec(v_a_4502_);
lean_dec_ref(v_a_4501_);
lean_dec(v_a_4500_);
lean_dec_ref(v_a_4499_);
lean_dec(v_a_4498_);
lean_dec_ref(v_a_4497_);
lean_dec(v_a_4496_);
lean_dec_ref(v_a_4495_);
lean_dec(v_a_4494_);
lean_dec(v_a_4493_);
lean_dec_ref(v_a_4492_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_mvarId_4505_, lean_object* v_val_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v___x_4509_; lean_object* v_mctx_4510_; lean_object* v_cache_4511_; lean_object* v_zetaDeltaFVarIds_4512_; lean_object* v_postponed_4513_; lean_object* v_diag_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4542_; 
v___x_4509_ = lean_st_ref_take(v___y_4507_);
v_mctx_4510_ = lean_ctor_get(v___x_4509_, 0);
v_cache_4511_ = lean_ctor_get(v___x_4509_, 1);
v_zetaDeltaFVarIds_4512_ = lean_ctor_get(v___x_4509_, 2);
v_postponed_4513_ = lean_ctor_get(v___x_4509_, 3);
v_diag_4514_ = lean_ctor_get(v___x_4509_, 4);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4516_ = v___x_4509_;
v_isShared_4517_ = v_isSharedCheck_4542_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_diag_4514_);
lean_inc(v_postponed_4513_);
lean_inc(v_zetaDeltaFVarIds_4512_);
lean_inc(v_cache_4511_);
lean_inc(v_mctx_4510_);
lean_dec(v___x_4509_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4542_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v_depth_4518_; lean_object* v_levelAssignDepth_4519_; lean_object* v_lmvarCounter_4520_; lean_object* v_mvarCounter_4521_; lean_object* v_lDecls_4522_; lean_object* v_decls_4523_; lean_object* v_userNames_4524_; lean_object* v_lAssignment_4525_; lean_object* v_eAssignment_4526_; lean_object* v_dAssignment_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4541_; 
v_depth_4518_ = lean_ctor_get(v_mctx_4510_, 0);
v_levelAssignDepth_4519_ = lean_ctor_get(v_mctx_4510_, 1);
v_lmvarCounter_4520_ = lean_ctor_get(v_mctx_4510_, 2);
v_mvarCounter_4521_ = lean_ctor_get(v_mctx_4510_, 3);
v_lDecls_4522_ = lean_ctor_get(v_mctx_4510_, 4);
v_decls_4523_ = lean_ctor_get(v_mctx_4510_, 5);
v_userNames_4524_ = lean_ctor_get(v_mctx_4510_, 6);
v_lAssignment_4525_ = lean_ctor_get(v_mctx_4510_, 7);
v_eAssignment_4526_ = lean_ctor_get(v_mctx_4510_, 8);
v_dAssignment_4527_ = lean_ctor_get(v_mctx_4510_, 9);
v_isSharedCheck_4541_ = !lean_is_exclusive(v_mctx_4510_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4529_ = v_mctx_4510_;
v_isShared_4530_ = v_isSharedCheck_4541_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_dAssignment_4527_);
lean_inc(v_eAssignment_4526_);
lean_inc(v_lAssignment_4525_);
lean_inc(v_userNames_4524_);
lean_inc(v_decls_4523_);
lean_inc(v_lDecls_4522_);
lean_inc(v_mvarCounter_4521_);
lean_inc(v_lmvarCounter_4520_);
lean_inc(v_levelAssignDepth_4519_);
lean_inc(v_depth_4518_);
lean_dec(v_mctx_4510_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4541_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4531_; lean_object* v___x_4533_; 
v___x_4531_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(v_eAssignment_4526_, v_mvarId_4505_, v_val_4506_);
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 8, v___x_4531_);
v___x_4533_ = v___x_4529_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_depth_4518_);
lean_ctor_set(v_reuseFailAlloc_4540_, 1, v_levelAssignDepth_4519_);
lean_ctor_set(v_reuseFailAlloc_4540_, 2, v_lmvarCounter_4520_);
lean_ctor_set(v_reuseFailAlloc_4540_, 3, v_mvarCounter_4521_);
lean_ctor_set(v_reuseFailAlloc_4540_, 4, v_lDecls_4522_);
lean_ctor_set(v_reuseFailAlloc_4540_, 5, v_decls_4523_);
lean_ctor_set(v_reuseFailAlloc_4540_, 6, v_userNames_4524_);
lean_ctor_set(v_reuseFailAlloc_4540_, 7, v_lAssignment_4525_);
lean_ctor_set(v_reuseFailAlloc_4540_, 8, v___x_4531_);
lean_ctor_set(v_reuseFailAlloc_4540_, 9, v_dAssignment_4527_);
v___x_4533_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4535_; 
if (v_isShared_4517_ == 0)
{
lean_ctor_set(v___x_4516_, 0, v___x_4533_);
v___x_4535_ = v___x_4516_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4533_);
lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_cache_4511_);
lean_ctor_set(v_reuseFailAlloc_4539_, 2, v_zetaDeltaFVarIds_4512_);
lean_ctor_set(v_reuseFailAlloc_4539_, 3, v_postponed_4513_);
lean_ctor_set(v_reuseFailAlloc_4539_, 4, v_diag_4514_);
v___x_4535_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4536_ = lean_st_ref_set(v___y_4507_, v___x_4535_);
v___x_4537_ = lean_box(0);
v___x_4538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4537_);
return v___x_4538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object* v_mvarId_4543_, lean_object* v_val_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_mvarId_4543_, v_val_4544_, v___y_4545_);
lean_dec(v___y_4545_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object* v_cls_4548_, lean_object* v_msg_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
lean_object* v_ref_4555_; lean_object* v___x_4556_; lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4601_; 
v_ref_4555_ = lean_ctor_get(v___y_4552_, 5);
v___x_4556_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4559_ = v___x_4556_;
v_isShared_4560_ = v_isSharedCheck_4601_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4556_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4601_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4561_; lean_object* v_traceState_4562_; lean_object* v_env_4563_; lean_object* v_nextMacroScope_4564_; lean_object* v_ngen_4565_; lean_object* v_auxDeclNGen_4566_; lean_object* v_cache_4567_; lean_object* v_messages_4568_; lean_object* v_infoState_4569_; lean_object* v_snapshotTasks_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4600_; 
v___x_4561_ = lean_st_ref_take(v___y_4553_);
v_traceState_4562_ = lean_ctor_get(v___x_4561_, 4);
v_env_4563_ = lean_ctor_get(v___x_4561_, 0);
v_nextMacroScope_4564_ = lean_ctor_get(v___x_4561_, 1);
v_ngen_4565_ = lean_ctor_get(v___x_4561_, 2);
v_auxDeclNGen_4566_ = lean_ctor_get(v___x_4561_, 3);
v_cache_4567_ = lean_ctor_get(v___x_4561_, 5);
v_messages_4568_ = lean_ctor_get(v___x_4561_, 6);
v_infoState_4569_ = lean_ctor_get(v___x_4561_, 7);
v_snapshotTasks_4570_ = lean_ctor_get(v___x_4561_, 8);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4572_ = v___x_4561_;
v_isShared_4573_ = v_isSharedCheck_4600_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_snapshotTasks_4570_);
lean_inc(v_infoState_4569_);
lean_inc(v_messages_4568_);
lean_inc(v_cache_4567_);
lean_inc(v_traceState_4562_);
lean_inc(v_auxDeclNGen_4566_);
lean_inc(v_ngen_4565_);
lean_inc(v_nextMacroScope_4564_);
lean_inc(v_env_4563_);
lean_dec(v___x_4561_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4600_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
uint64_t v_tid_4574_; lean_object* v_traces_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4599_; 
v_tid_4574_ = lean_ctor_get_uint64(v_traceState_4562_, sizeof(void*)*1);
v_traces_4575_ = lean_ctor_get(v_traceState_4562_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_traceState_4562_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4577_ = v_traceState_4562_;
v_isShared_4578_ = v_isSharedCheck_4599_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_traces_4575_);
lean_dec(v_traceState_4562_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4599_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4579_; double v___x_4580_; uint8_t v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4589_; 
v___x_4579_ = lean_box(0);
v___x_4580_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_4581_ = 0;
v___x_4582_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4583_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4583_, 0, v_cls_4548_);
lean_ctor_set(v___x_4583_, 1, v___x_4579_);
lean_ctor_set(v___x_4583_, 2, v___x_4582_);
lean_ctor_set_float(v___x_4583_, sizeof(void*)*3, v___x_4580_);
lean_ctor_set_float(v___x_4583_, sizeof(void*)*3 + 8, v___x_4580_);
lean_ctor_set_uint8(v___x_4583_, sizeof(void*)*3 + 16, v___x_4581_);
v___x_4584_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_4585_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4583_);
lean_ctor_set(v___x_4585_, 1, v_a_4557_);
lean_ctor_set(v___x_4585_, 2, v___x_4584_);
lean_inc(v_ref_4555_);
v___x_4586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4586_, 0, v_ref_4555_);
lean_ctor_set(v___x_4586_, 1, v___x_4585_);
v___x_4587_ = l_Lean_PersistentArray_push___redArg(v_traces_4575_, v___x_4586_);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v___x_4587_);
v___x_4589_ = v___x_4577_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4587_);
lean_ctor_set_uint64(v_reuseFailAlloc_4598_, sizeof(void*)*1, v_tid_4574_);
v___x_4589_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
lean_object* v___x_4591_; 
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 4, v___x_4589_);
v___x_4591_ = v___x_4572_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_env_4563_);
lean_ctor_set(v_reuseFailAlloc_4597_, 1, v_nextMacroScope_4564_);
lean_ctor_set(v_reuseFailAlloc_4597_, 2, v_ngen_4565_);
lean_ctor_set(v_reuseFailAlloc_4597_, 3, v_auxDeclNGen_4566_);
lean_ctor_set(v_reuseFailAlloc_4597_, 4, v___x_4589_);
lean_ctor_set(v_reuseFailAlloc_4597_, 5, v_cache_4567_);
lean_ctor_set(v_reuseFailAlloc_4597_, 6, v_messages_4568_);
lean_ctor_set(v_reuseFailAlloc_4597_, 7, v_infoState_4569_);
lean_ctor_set(v_reuseFailAlloc_4597_, 8, v_snapshotTasks_4570_);
v___x_4591_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4595_; 
v___x_4592_ = lean_st_ref_set(v___y_4553_, v___x_4591_);
v___x_4593_ = lean_box(0);
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 0, v___x_4593_);
v___x_4595_ = v___x_4559_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4593_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_4602_, lean_object* v_msg_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
lean_object* v_res_4609_; 
v_res_4609_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_4602_, v_msg_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(lean_object* v_upperBound_4610_, lean_object* v___x_4611_, lean_object* v_methods_4612_, lean_object* v_config_4613_, lean_object* v_a_4614_, lean_object* v_b_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_){
_start:
{
lean_object* v___y_4630_; uint8_t v___x_4652_; 
v___x_4652_ = lean_nat_dec_lt(v_a_4614_, v_upperBound_4610_);
if (v___x_4652_ == 0)
{
lean_object* v___x_4653_; 
lean_dec(v_a_4614_);
lean_dec_ref(v_config_4613_);
lean_dec_ref(v_methods_4612_);
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v_b_4615_);
return v___x_4653_;
}
else
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v_type_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4654_ = lean_st_ref_take(v___y_4616_);
v___x_4655_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
v___x_4656_ = lean_st_ref_set(v___y_4616_, v___x_4655_);
v___x_4657_ = lean_array_fget_borrowed(v___x_4611_, v_a_4614_);
v_type_4658_ = lean_ctor_get(v___x_4657_, 1);
v___x_4659_ = lean_unsigned_to_nat(0u);
v___x_4660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4659_);
lean_ctor_set(v___x_4660_, 1, v___x_4654_);
lean_inc_ref(v_type_4658_);
v___x_4661_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4661_, 0, v_type_4658_);
lean_inc_ref(v_config_4613_);
lean_inc_ref(v_methods_4612_);
v___x_4662_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4661_, v_methods_4612_, v_config_4613_, v___x_4660_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v_snd_4664_; lean_object* v_fst_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4755_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4663_);
lean_dec_ref_known(v___x_4662_, 1);
v_snd_4664_ = lean_ctor_get(v_a_4663_, 1);
v_fst_4665_ = lean_ctor_get(v_a_4663_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v_a_4663_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4667_ = v_a_4663_;
v_isShared_4668_ = v_isSharedCheck_4755_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_snd_4664_);
lean_inc(v_fst_4665_);
lean_dec(v_a_4663_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4755_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v_cache_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4753_; 
v_cache_4669_ = lean_ctor_get(v_snd_4664_, 1);
v_isSharedCheck_4753_ = !lean_is_exclusive(v_snd_4664_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; 
v_unused_4754_ = lean_ctor_get(v_snd_4664_, 0);
lean_dec(v_unused_4754_);
v___x_4671_ = v_snd_4664_;
v_isShared_4672_ = v_isSharedCheck_4753_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_cache_4669_);
lean_dec(v_snd_4664_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4753_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4673_ = lean_st_ref_set(v___y_4616_, v_cache_4669_);
lean_inc(v___x_4657_);
v___x_4674_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_4657_, v_fst_4665_);
lean_dec(v_fst_4665_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; lean_object* v_snd_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4743_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v___x_4674_, 1);
v_snd_4676_ = lean_ctor_get(v_b_4615_, 1);
v_isSharedCheck_4743_ = !lean_is_exclusive(v_b_4615_);
if (v_isSharedCheck_4743_ == 0)
{
lean_object* v_unused_4744_; 
v_unused_4744_ = lean_ctor_get(v_b_4615_, 0);
lean_dec(v_unused_4744_);
v___x_4678_ = v_b_4615_;
v_isShared_4679_ = v_isSharedCheck_4743_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_snd_4676_);
lean_dec(v_b_4615_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4743_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v_type_4680_; lean_object* v_value_4681_; uint8_t v___x_4682_; 
v_type_4680_ = lean_ctor_get(v_a_4675_, 1);
v_value_4681_ = lean_ctor_get(v_a_4675_, 2);
lean_inc_ref(v_type_4680_);
v___x_4682_ = l_Lean_Expr_isFalse(v_type_4680_);
if (v___x_4682_ == 0)
{
lean_object* v___x_4683_; lean_object* v___f_4684_; uint8_t v___x_4715_; 
lean_del_object(v___x_4678_);
v___x_4683_ = lean_box(0);
lean_inc(v_a_4675_);
lean_inc(v_snd_4676_);
v___f_4684_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0___boxed), 17, 3);
lean_closure_set(v___f_4684_, 0, v_snd_4676_);
lean_closure_set(v___f_4684_, 1, v_a_4675_);
lean_closure_set(v___f_4684_, 2, v___x_4683_);
v___x_4715_ = lean_expr_eqv(v_type_4658_, v_type_4680_);
if (v___x_4715_ == 0)
{
lean_inc_ref(v_type_4680_);
lean_dec(v_snd_4676_);
lean_dec(v_a_4675_);
goto v___jp_4688_;
}
else
{
if (v___x_4682_ == 0)
{
lean_object* v___x_4716_; lean_object* v___x_4717_; 
lean_dec_ref(v___f_4684_);
lean_del_object(v___x_4671_);
lean_del_object(v___x_4667_);
v___x_4716_ = lean_box(0);
v___x_4717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(v_snd_4676_, v_a_4675_, v___x_4683_, v___x_4716_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
v___y_4630_ = v___x_4717_;
goto v___jp_4629_;
}
else
{
lean_inc_ref(v_type_4680_);
lean_dec(v_snd_4676_);
lean_dec(v_a_4675_);
goto v___jp_4688_;
}
}
v___jp_4685_:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4686_ = lean_box(0);
v___x_4687_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_4652_, v___f_4684_, v___x_4686_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
v___y_4630_ = v___x_4687_;
goto v___jp_4629_;
}
v___jp_4688_:
{
lean_object* v_options_4689_; uint8_t v_hasTrace_4690_; 
v_options_4689_ = lean_ctor_get(v___y_4626_, 2);
v_hasTrace_4690_ = lean_ctor_get_uint8(v_options_4689_, sizeof(void*)*1);
if (v_hasTrace_4690_ == 0)
{
lean_dec_ref(v_type_4680_);
lean_del_object(v___x_4671_);
lean_del_object(v___x_4667_);
goto v___jp_4685_;
}
else
{
lean_object* v_inheritedTraceOptions_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; uint8_t v___x_4694_; 
v_inheritedTraceOptions_4691_ = lean_ctor_get(v___y_4626_, 13);
v___x_4692_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
v___x_4693_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___x_4694_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4691_, v_options_4689_, v___x_4693_);
if (v___x_4694_ == 0)
{
lean_dec_ref(v_type_4680_);
lean_del_object(v___x_4671_);
lean_del_object(v___x_4667_);
goto v___jp_4685_;
}
else
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4698_; 
lean_inc_ref(v_type_4658_);
v___x_4695_ = l_Lean_MessageData_ofExpr(v_type_4658_);
v___x_4696_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_4672_ == 0)
{
lean_ctor_set_tag(v___x_4671_, 7);
lean_ctor_set(v___x_4671_, 1, v___x_4696_);
lean_ctor_set(v___x_4671_, 0, v___x_4695_);
v___x_4698_ = v___x_4671_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v___x_4695_);
lean_ctor_set(v_reuseFailAlloc_4714_, 1, v___x_4696_);
v___x_4698_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
lean_object* v___x_4699_; lean_object* v___x_4701_; 
v___x_4699_ = l_Lean_MessageData_ofExpr(v_type_4680_);
if (v_isShared_4668_ == 0)
{
lean_ctor_set_tag(v___x_4667_, 7);
lean_ctor_set(v___x_4667_, 1, v___x_4699_);
lean_ctor_set(v___x_4667_, 0, v___x_4698_);
v___x_4701_ = v___x_4667_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4698_);
lean_ctor_set(v_reuseFailAlloc_4713_, 1, v___x_4699_);
v___x_4701_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
lean_object* v___x_4702_; 
v___x_4702_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_4692_, v___x_4701_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
if (lean_obj_tag(v___x_4702_) == 0)
{
lean_object* v_a_4703_; lean_object* v___x_4704_; 
v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_a_4703_);
lean_dec_ref_known(v___x_4702_, 1);
v___x_4704_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_4652_, v___f_4684_, v_a_4703_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
v___y_4630_ = v___x_4704_;
goto v___jp_4629_;
}
else
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec_ref(v___f_4684_);
lean_dec(v_a_4614_);
lean_dec_ref(v_config_4613_);
lean_dec_ref(v_methods_4612_);
v_a_4705_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4702_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4702_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
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
lean_object* v___x_4718_; lean_object* v_target_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
lean_inc_ref(v_value_4681_);
lean_dec(v_a_4675_);
lean_del_object(v___x_4671_);
lean_del_object(v___x_4667_);
lean_dec(v_a_4614_);
lean_dec_ref(v_config_4613_);
lean_dec_ref(v_methods_4612_);
v___x_4718_ = lean_st_ref_get(v___y_4618_);
v_target_4719_ = lean_ctor_get(v___x_4718_, 4);
lean_inc_ref(v_target_4719_);
lean_dec(v___x_4718_);
v___x_4720_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_4719_);
lean_dec_ref(v_target_4719_);
v___x_4721_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v___x_4720_, v_value_4681_, v___y_4625_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4733_; 
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4733_ == 0)
{
lean_object* v_unused_4734_; 
v_unused_4734_ = lean_ctor_get(v___x_4721_, 0);
lean_dec(v_unused_4734_);
v___x_4723_ = v___x_4721_;
v_isShared_4724_ = v_isSharedCheck_4733_;
goto v_resetjp_4722_;
}
else
{
lean_dec(v___x_4721_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4733_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4728_; 
v___x_4725_ = lean_box(v___x_4682_);
v___x_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4725_);
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 0, v___x_4726_);
v___x_4728_ = v___x_4678_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v___x_4726_);
lean_ctor_set(v_reuseFailAlloc_4732_, 1, v_snd_4676_);
v___x_4728_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
lean_object* v___x_4730_; 
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 0, v___x_4728_);
v___x_4730_ = v___x_4723_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v___x_4728_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
}
else
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
lean_del_object(v___x_4678_);
lean_dec(v_snd_4676_);
v_a_4735_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4737_ = v___x_4721_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4721_);
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
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4752_; 
lean_del_object(v___x_4671_);
lean_del_object(v___x_4667_);
lean_dec_ref(v_b_4615_);
lean_dec(v_a_4614_);
lean_dec_ref(v_config_4613_);
lean_dec_ref(v_methods_4612_);
v_a_4745_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4747_ = v___x_4674_;
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4674_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
if (v_isShared_4748_ == 0)
{
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
}
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_dec_ref(v_b_4615_);
lean_dec(v_a_4614_);
lean_dec_ref(v_config_4613_);
lean_dec_ref(v_methods_4612_);
v_a_4756_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4662_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4662_);
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
v___jp_4629_:
{
if (lean_obj_tag(v___y_4630_) == 0)
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4643_; 
v_a_4631_ = lean_ctor_get(v___y_4630_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___y_4630_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4633_ = v___y_4630_;
v_isShared_4634_ = v_isSharedCheck_4643_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___y_4630_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4643_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
if (lean_obj_tag(v_a_4631_) == 0)
{
lean_object* v_a_4635_; lean_object* v___x_4637_; 
lean_dec(v_a_4614_);
lean_dec_ref(v_config_4613_);
lean_dec_ref(v_methods_4612_);
v_a_4635_ = lean_ctor_get(v_a_4631_, 0);
lean_inc(v_a_4635_);
lean_dec_ref_known(v_a_4631_, 1);
if (v_isShared_4634_ == 0)
{
lean_ctor_set(v___x_4633_, 0, v_a_4635_);
v___x_4637_ = v___x_4633_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4635_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; 
lean_del_object(v___x_4633_);
v_a_4639_ = lean_ctor_get(v_a_4631_, 0);
lean_inc(v_a_4639_);
lean_dec_ref_known(v_a_4631_, 1);
v___x_4640_ = lean_unsigned_to_nat(1u);
v___x_4641_ = lean_nat_add(v_a_4614_, v___x_4640_);
lean_dec(v_a_4614_);
v_a_4614_ = v___x_4641_;
v_b_4615_ = v_a_4639_;
goto _start;
}
}
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
lean_dec(v_a_4614_);
lean_dec_ref(v_config_4613_);
lean_dec_ref(v_methods_4612_);
v_a_4644_ = lean_ctor_get(v___y_4630_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___y_4630_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___y_4630_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___y_4630_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_4764_ = _args[0];
lean_object* v___x_4765_ = _args[1];
lean_object* v_methods_4766_ = _args[2];
lean_object* v_config_4767_ = _args[3];
lean_object* v_a_4768_ = _args[4];
lean_object* v_b_4769_ = _args[5];
lean_object* v___y_4770_ = _args[6];
lean_object* v___y_4771_ = _args[7];
lean_object* v___y_4772_ = _args[8];
lean_object* v___y_4773_ = _args[9];
lean_object* v___y_4774_ = _args[10];
lean_object* v___y_4775_ = _args[11];
lean_object* v___y_4776_ = _args[12];
lean_object* v___y_4777_ = _args[13];
lean_object* v___y_4778_ = _args[14];
lean_object* v___y_4779_ = _args[15];
lean_object* v___y_4780_ = _args[16];
lean_object* v___y_4781_ = _args[17];
lean_object* v___y_4782_ = _args[18];
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(v_upperBound_4764_, v___x_4765_, v_methods_4766_, v_config_4767_, v_a_4768_, v_b_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec(v___y_4779_);
lean_dec_ref(v___y_4778_);
lean_dec(v___y_4777_);
lean_dec_ref(v___y_4776_);
lean_dec(v___y_4775_);
lean_dec_ref(v___y_4774_);
lean_dec(v___y_4773_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec(v___y_4770_);
lean_dec_ref(v___x_4765_);
lean_dec(v_upperBound_4764_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_4784_, lean_object* v_config_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_){
_start:
{
lean_object* v___x_4799_; lean_object* v_hypotheses_4800_; lean_object* v___x_4801_; lean_object* v_newHyps_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4799_ = lean_st_ref_get(v_a_4788_);
v_hypotheses_4800_ = lean_ctor_get(v___x_4799_, 5);
lean_inc_ref(v_hypotheses_4800_);
lean_dec(v___x_4799_);
v___x_4801_ = lean_array_get_size(v_hypotheses_4800_);
v_newHyps_4802_ = lean_mk_empty_array_with_capacity(v___x_4801_);
v___x_4803_ = lean_unsigned_to_nat(0u);
v___x_4804_ = lean_box(0);
v___x_4805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4805_, 0, v___x_4804_);
lean_ctor_set(v___x_4805_, 1, v_newHyps_4802_);
v___x_4806_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(v___x_4801_, v_hypotheses_4800_, v_methods_4784_, v_config_4785_, v___x_4803_, v___x_4805_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_);
lean_dec_ref(v_hypotheses_4800_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4838_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4838_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4838_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v_fst_4811_; 
v_fst_4811_ = lean_ctor_get(v_a_4807_, 0);
if (lean_obj_tag(v_fst_4811_) == 0)
{
lean_object* v_snd_4812_; lean_object* v___x_4813_; lean_object* v_rewriteSimpCache_4814_; lean_object* v_rewriteDSimpCache_4815_; lean_object* v_acCache_4816_; lean_object* v_typeAnalysis_4817_; lean_object* v_target_4818_; uint8_t v_didChange_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4832_; 
v_snd_4812_ = lean_ctor_get(v_a_4807_, 1);
lean_inc(v_snd_4812_);
lean_dec(v_a_4807_);
v___x_4813_ = lean_st_ref_take(v_a_4788_);
v_rewriteSimpCache_4814_ = lean_ctor_get(v___x_4813_, 0);
v_rewriteDSimpCache_4815_ = lean_ctor_get(v___x_4813_, 1);
v_acCache_4816_ = lean_ctor_get(v___x_4813_, 2);
v_typeAnalysis_4817_ = lean_ctor_get(v___x_4813_, 3);
v_target_4818_ = lean_ctor_get(v___x_4813_, 4);
v_didChange_4819_ = lean_ctor_get_uint8(v___x_4813_, sizeof(void*)*6);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4832_ == 0)
{
lean_object* v_unused_4833_; 
v_unused_4833_ = lean_ctor_get(v___x_4813_, 5);
lean_dec(v_unused_4833_);
v___x_4821_ = v___x_4813_;
v_isShared_4822_ = v_isSharedCheck_4832_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_target_4818_);
lean_inc(v_typeAnalysis_4817_);
lean_inc(v_acCache_4816_);
lean_inc(v_rewriteDSimpCache_4815_);
lean_inc(v_rewriteSimpCache_4814_);
lean_dec(v___x_4813_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4832_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 5, v_snd_4812_);
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_rewriteSimpCache_4814_);
lean_ctor_set(v_reuseFailAlloc_4831_, 1, v_rewriteDSimpCache_4815_);
lean_ctor_set(v_reuseFailAlloc_4831_, 2, v_acCache_4816_);
lean_ctor_set(v_reuseFailAlloc_4831_, 3, v_typeAnalysis_4817_);
lean_ctor_set(v_reuseFailAlloc_4831_, 4, v_target_4818_);
lean_ctor_set(v_reuseFailAlloc_4831_, 5, v_snd_4812_);
lean_ctor_set_uint8(v_reuseFailAlloc_4831_, sizeof(void*)*6, v_didChange_4819_);
v___x_4824_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
lean_object* v___x_4825_; uint8_t v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4829_; 
v___x_4825_ = lean_st_ref_set(v_a_4788_, v___x_4824_);
v___x_4826_ = 0;
v___x_4827_ = lean_box(v___x_4826_);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4827_);
v___x_4829_ = v___x_4809_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4827_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
else
{
lean_object* v_val_4834_; lean_object* v___x_4836_; 
lean_inc_ref(v_fst_4811_);
lean_dec(v_a_4807_);
v_val_4834_ = lean_ctor_get(v_fst_4811_, 0);
lean_inc(v_val_4834_);
lean_dec_ref_known(v_fst_4811_, 1);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v_val_4834_);
v___x_4836_ = v___x_4809_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_val_4834_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
v_a_4839_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4806_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4806_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4844_; 
if (v_isShared_4842_ == 0)
{
v___x_4844_ = v___x_4841_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_4847_, lean_object* v_config_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_4847_, v_config_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_);
lean_dec(v_a_4860_);
lean_dec_ref(v_a_4859_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_4863_, lean_object* v_msg_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_){
_start:
{
lean_object* v___x_4878_; 
v___x_4878_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_4863_, v_msg_4864_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_4879_, lean_object* v_msg_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_4879_, v_msg_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
lean_dec(v___y_4892_);
lean_dec_ref(v___y_4891_);
lean_dec(v___y_4890_);
lean_dec_ref(v___y_4889_);
lean_dec(v___y_4888_);
lean_dec_ref(v___y_4887_);
lean_dec(v___y_4886_);
lean_dec_ref(v___y_4885_);
lean_dec(v___y_4884_);
lean_dec(v___y_4883_);
lean_dec_ref(v___y_4882_);
lean_dec(v___y_4881_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_mvarId_4895_, lean_object* v_val_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_mvarId_4895_, v_val_4896_, v___y_4906_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object* v_mvarId_4911_, lean_object* v_val_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_mvarId_4911_, v_val_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_);
lean_dec(v___y_4924_);
lean_dec_ref(v___y_4923_);
lean_dec(v___y_4922_);
lean_dec_ref(v___y_4921_);
lean_dec(v___y_4920_);
lean_dec_ref(v___y_4919_);
lean_dec(v___y_4918_);
lean_dec_ref(v___y_4917_);
lean_dec(v___y_4916_);
lean_dec(v___y_4915_);
lean_dec_ref(v___y_4914_);
lean_dec(v___y_4913_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2(lean_object* v_upperBound_4927_, lean_object* v___x_4928_, lean_object* v_methods_4929_, lean_object* v_config_4930_, lean_object* v_inst_4931_, lean_object* v_R_4932_, lean_object* v_a_4933_, lean_object* v_b_4934_, lean_object* v_c_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(v_upperBound_4927_, v___x_4928_, v_methods_4929_, v_config_4930_, v_a_4933_, v_b_4934_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_4950_ = _args[0];
lean_object* v___x_4951_ = _args[1];
lean_object* v_methods_4952_ = _args[2];
lean_object* v_config_4953_ = _args[3];
lean_object* v_inst_4954_ = _args[4];
lean_object* v_R_4955_ = _args[5];
lean_object* v_a_4956_ = _args[6];
lean_object* v_b_4957_ = _args[7];
lean_object* v_c_4958_ = _args[8];
lean_object* v___y_4959_ = _args[9];
lean_object* v___y_4960_ = _args[10];
lean_object* v___y_4961_ = _args[11];
lean_object* v___y_4962_ = _args[12];
lean_object* v___y_4963_ = _args[13];
lean_object* v___y_4964_ = _args[14];
lean_object* v___y_4965_ = _args[15];
lean_object* v___y_4966_ = _args[16];
lean_object* v___y_4967_ = _args[17];
lean_object* v___y_4968_ = _args[18];
lean_object* v___y_4969_ = _args[19];
lean_object* v___y_4970_ = _args[20];
lean_object* v___y_4971_ = _args[21];
_start:
{
lean_object* v_res_4972_; 
v_res_4972_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2(v_upperBound_4950_, v___x_4951_, v_methods_4952_, v_config_4953_, v_inst_4954_, v_R_4955_, v_a_4956_, v_b_4957_, v_c_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_);
lean_dec(v___y_4970_);
lean_dec_ref(v___y_4969_);
lean_dec(v___y_4968_);
lean_dec_ref(v___y_4967_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec(v___y_4964_);
lean_dec_ref(v___y_4963_);
lean_dec(v___y_4962_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec(v___y_4959_);
lean_dec_ref(v___x_4951_);
lean_dec(v_upperBound_4950_);
return v_res_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_4973_, lean_object* v_config_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_){
_start:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4987_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
v___x_4988_ = lean_st_mk_ref(v___x_4987_);
v___x_4989_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_4973_, v_config_4974_, v___x_4988_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
if (lean_obj_tag(v___x_4989_) == 0)
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4998_; 
v_a_4990_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4992_ = v___x_4989_;
v_isShared_4993_ = v_isSharedCheck_4998_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4989_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4998_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4994_; lean_object* v___x_4996_; 
v___x_4994_ = lean_st_ref_get(v___x_4988_);
lean_dec(v___x_4988_);
lean_dec(v___x_4994_);
if (v_isShared_4993_ == 0)
{
v___x_4996_ = v___x_4992_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_a_4990_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
else
{
lean_dec(v___x_4988_);
return v___x_4989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_4999_, lean_object* v_config_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_4999_, v_config_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_);
lean_dec(v_a_5011_);
lean_dec_ref(v_a_5010_);
lean_dec(v_a_5009_);
lean_dec_ref(v_a_5008_);
lean_dec(v_a_5007_);
lean_dec_ref(v_a_5006_);
lean_dec(v_a_5005_);
lean_dec_ref(v_a_5004_);
lean_dec(v_a_5003_);
lean_dec(v_a_5002_);
lean_dec_ref(v_a_5001_);
return v_res_5013_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5015_; lean_object* v___x_5016_; 
v___x_5015_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_5016_ = l_Lean_stringToMessageData(v___x_5015_);
return v___x_5016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_5017_, lean_object* v_x_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5031_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_5032_ = l_Lean_MessageData_ofName(v_name_5017_);
v___x_5033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5033_, 0, v___x_5031_);
lean_ctor_set(v___x_5033_, 1, v___x_5032_);
v___x_5034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5034_, 0, v___x_5033_);
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_5035_, lean_object* v_x_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_){
_start:
{
lean_object* v_res_5049_; 
v_res_5049_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_5035_, v_x_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_);
lean_dec(v___y_5047_);
lean_dec_ref(v___y_5046_);
lean_dec(v___y_5045_);
lean_dec_ref(v___y_5044_);
lean_dec(v___y_5043_);
lean_dec_ref(v___y_5042_);
lean_dec(v___y_5041_);
lean_dec_ref(v___y_5040_);
lean_dec(v___y_5039_);
lean_dec(v___y_5038_);
lean_dec_ref(v___y_5037_);
lean_dec_ref(v_x_5036_);
return v_res_5049_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_5050_; 
v___x_5050_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_5050_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_5051_; lean_object* v___x_5052_; 
v___x_5051_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_5052_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5051_);
return v___x_5052_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5053_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_5054_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5053_);
return v___x_5054_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5055_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_5056_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5055_);
return v___x_5056_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; 
v___x_5057_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_5058_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5057_);
return v___x_5058_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5059_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_5060_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5059_);
return v___x_5060_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; 
v___x_5061_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_5062_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5061_);
return v___x_5062_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_5064_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5063_);
return v___x_5064_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5065_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_5066_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5065_);
return v___x_5066_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9(void){
_start:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v___x_5068_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5067_);
return v___x_5068_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5069_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9);
v___x_5070_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_5069_);
return v___x_5070_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11(void){
_start:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5071_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_5072_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_5071_);
return v___x_5072_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13(void){
_start:
{
lean_object* v___x_5074_; double v___x_5075_; 
v___x_5074_ = lean_unsigned_to_nat(1000000000u);
v___x_5075_ = lean_float_of_nat(v___x_5074_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_){
_start:
{
lean_object* v___x_5089_; lean_object* v_toApplicative_5090_; lean_object* v_toFunctor_5091_; lean_object* v_toSeq_5092_; lean_object* v_toSeqLeft_5093_; lean_object* v_toSeqRight_5094_; lean_object* v___f_5095_; lean_object* v___f_5096_; lean_object* v___f_5097_; lean_object* v___f_5098_; lean_object* v___x_5099_; lean_object* v___f_5100_; lean_object* v___f_5101_; lean_object* v___f_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v_toApplicative_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5250_; 
v___x_5089_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1);
v_toApplicative_5090_ = lean_ctor_get(v___x_5089_, 0);
v_toFunctor_5091_ = lean_ctor_get(v_toApplicative_5090_, 0);
v_toSeq_5092_ = lean_ctor_get(v_toApplicative_5090_, 2);
v_toSeqLeft_5093_ = lean_ctor_get(v_toApplicative_5090_, 3);
v_toSeqRight_5094_ = lean_ctor_get(v_toApplicative_5090_, 4);
v___f_5095_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2));
v___f_5096_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3));
lean_inc_ref_n(v_toFunctor_5091_, 2);
v___f_5097_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5097_, 0, v_toFunctor_5091_);
v___f_5098_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5098_, 0, v_toFunctor_5091_);
v___x_5099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5099_, 0, v___f_5097_);
lean_ctor_set(v___x_5099_, 1, v___f_5098_);
lean_inc(v_toSeqRight_5094_);
v___f_5100_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5100_, 0, v_toSeqRight_5094_);
lean_inc(v_toSeqLeft_5093_);
v___f_5101_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5101_, 0, v_toSeqLeft_5093_);
lean_inc(v_toSeq_5092_);
v___f_5102_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5102_, 0, v_toSeq_5092_);
v___x_5103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5103_, 0, v___x_5099_);
lean_ctor_set(v___x_5103_, 1, v___f_5095_);
lean_ctor_set(v___x_5103_, 2, v___f_5102_);
lean_ctor_set(v___x_5103_, 3, v___f_5101_);
lean_ctor_set(v___x_5103_, 4, v___f_5100_);
v___x_5104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5104_, 0, v___x_5103_);
lean_ctor_set(v___x_5104_, 1, v___f_5096_);
v___x_5105_ = l_StateRefT_x27_instMonad___redArg(v___x_5104_);
v_toApplicative_5106_ = lean_ctor_get(v___x_5105_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5250_ == 0)
{
lean_object* v_unused_5251_; 
v_unused_5251_ = lean_ctor_get(v___x_5105_, 1);
lean_dec(v_unused_5251_);
v___x_5108_ = v___x_5105_;
v_isShared_5109_ = v_isSharedCheck_5250_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_toApplicative_5106_);
lean_dec(v___x_5105_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5250_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v_toFunctor_5110_; lean_object* v_toSeq_5111_; lean_object* v_toSeqLeft_5112_; lean_object* v_toSeqRight_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5248_; 
v_toFunctor_5110_ = lean_ctor_get(v_toApplicative_5106_, 0);
v_toSeq_5111_ = lean_ctor_get(v_toApplicative_5106_, 2);
v_toSeqLeft_5112_ = lean_ctor_get(v_toApplicative_5106_, 3);
v_toSeqRight_5113_ = lean_ctor_get(v_toApplicative_5106_, 4);
v_isSharedCheck_5248_ = !lean_is_exclusive(v_toApplicative_5106_);
if (v_isSharedCheck_5248_ == 0)
{
lean_object* v_unused_5249_; 
v_unused_5249_ = lean_ctor_get(v_toApplicative_5106_, 1);
lean_dec(v_unused_5249_);
v___x_5115_ = v_toApplicative_5106_;
v_isShared_5116_ = v_isSharedCheck_5248_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_toSeqRight_5113_);
lean_inc(v_toSeqLeft_5112_);
lean_inc(v_toSeq_5111_);
lean_inc(v_toFunctor_5110_);
lean_dec(v_toApplicative_5106_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5248_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___f_5117_; lean_object* v___f_5118_; lean_object* v___f_5119_; lean_object* v___f_5120_; lean_object* v___x_5121_; lean_object* v___f_5122_; lean_object* v___f_5123_; lean_object* v___f_5124_; lean_object* v___x_5126_; 
v___f_5117_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4));
v___f_5118_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5));
lean_inc_ref(v_toFunctor_5110_);
v___f_5119_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5119_, 0, v_toFunctor_5110_);
v___f_5120_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5120_, 0, v_toFunctor_5110_);
v___x_5121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5121_, 0, v___f_5119_);
lean_ctor_set(v___x_5121_, 1, v___f_5120_);
v___f_5122_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5122_, 0, v_toSeqRight_5113_);
v___f_5123_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5123_, 0, v_toSeqLeft_5112_);
v___f_5124_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5124_, 0, v_toSeq_5111_);
if (v_isShared_5116_ == 0)
{
lean_ctor_set(v___x_5115_, 4, v___f_5122_);
lean_ctor_set(v___x_5115_, 3, v___f_5123_);
lean_ctor_set(v___x_5115_, 2, v___f_5124_);
lean_ctor_set(v___x_5115_, 1, v___f_5117_);
lean_ctor_set(v___x_5115_, 0, v___x_5121_);
v___x_5126_ = v___x_5115_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5121_);
lean_ctor_set(v_reuseFailAlloc_5247_, 1, v___f_5117_);
lean_ctor_set(v_reuseFailAlloc_5247_, 2, v___f_5124_);
lean_ctor_set(v_reuseFailAlloc_5247_, 3, v___f_5123_);
lean_ctor_set(v_reuseFailAlloc_5247_, 4, v___f_5122_);
v___x_5126_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
lean_object* v___x_5128_; 
if (v_isShared_5109_ == 0)
{
lean_ctor_set(v___x_5108_, 1, v___f_5118_);
lean_ctor_set(v___x_5108_, 0, v___x_5126_);
v___x_5128_ = v___x_5108_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___x_5126_);
lean_ctor_set(v_reuseFailAlloc_5246_, 1, v___f_5118_);
v___x_5128_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v_toMonadRef_5138_; lean_object* v___x_5139_; lean_object* v_options_5140_; uint8_t v_hasTrace_5141_; 
v___x_5129_ = l_StateRefT_x27_instMonad___redArg(v___x_5128_);
v___x_5130_ = l_ReaderT_instMonad___redArg(v___x_5129_);
v___x_5131_ = l_StateRefT_x27_instMonad___redArg(v___x_5130_);
v___x_5132_ = l_ReaderT_instMonad___redArg(v___x_5131_);
v___x_5133_ = l_ReaderT_instMonad___redArg(v___x_5132_);
v___x_5134_ = l_StateRefT_x27_instMonad___redArg(v___x_5133_);
v___x_5135_ = l_ReaderT_instMonad___redArg(v___x_5134_);
v___x_5136_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16);
v___x_5137_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34);
v_toMonadRef_5138_ = lean_ctor_get(v___x_5137_, 0);
v___x_5139_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11);
v_options_5140_ = lean_ctor_get(v_a_5086_, 2);
v_hasTrace_5141_ = lean_ctor_get_uint8(v_options_5140_, sizeof(void*)*1);
if (v_hasTrace_5141_ == 0)
{
lean_object* v_run_x27_5142_; lean_object* v___x_5143_; 
lean_dec_ref(v___x_5135_);
v_run_x27_5142_ = lean_ctor_get(v_pass_5076_, 1);
lean_inc_ref(v_run_x27_5142_);
lean_dec_ref(v_pass_5076_);
lean_inc(v_a_5087_);
lean_inc_ref(v_a_5086_);
lean_inc(v_a_5085_);
lean_inc_ref(v_a_5084_);
lean_inc(v_a_5083_);
lean_inc_ref(v_a_5082_);
lean_inc(v_a_5081_);
lean_inc_ref(v_a_5080_);
lean_inc(v_a_5079_);
lean_inc(v_a_5078_);
lean_inc_ref(v_a_5077_);
v___x_5143_ = lean_apply_12(v_run_x27_5142_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, lean_box(0));
return v___x_5143_;
}
else
{
lean_object* v_name_5144_; lean_object* v_run_x27_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5245_; 
v_name_5144_ = lean_ctor_get(v_pass_5076_, 0);
v_run_x27_5145_ = lean_ctor_get(v_pass_5076_, 1);
v_isSharedCheck_5245_ = !lean_is_exclusive(v_pass_5076_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5147_ = v_pass_5076_;
v_isShared_5148_ = v_isSharedCheck_5245_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_run_x27_5145_);
lean_inc(v_name_5144_);
lean_dec(v_pass_5076_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5245_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v_inheritedTraceOptions_5149_; lean_object* v___f_5150_; lean_object* v___f_5151_; lean_object* v___f_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; uint8_t v___x_5156_; lean_object* v___y_5158_; lean_object* v___y_5159_; lean_object* v_a_5160_; lean_object* v___y_5176_; lean_object* v___y_5177_; lean_object* v_a_5178_; 
v_inheritedTraceOptions_5149_ = lean_ctor_get(v_a_5086_, 13);
v___f_5150_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_5150_, 0, v_name_5144_);
v___f_5151_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__41, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__41_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__41);
v___f_5152_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12));
v___x_5153_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
v___x_5154_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5155_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___x_5156_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5149_, v_options_5140_, v___x_5155_);
if (v___x_5156_ == 0)
{
lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; uint8_t v___x_5243_; 
v___x_5240_ = l_Lean_KVMap_instValueBool;
v___x_5241_ = l_Lean_trace_profiler;
v___x_5242_ = l_Lean_Option_get___redArg(v___x_5240_, v_options_5140_, v___x_5241_);
v___x_5243_ = lean_unbox(v___x_5242_);
lean_dec(v___x_5242_);
if (v___x_5243_ == 0)
{
lean_object* v___x_5244_; 
lean_dec_ref(v___f_5150_);
lean_del_object(v___x_5147_);
lean_dec_ref(v___x_5135_);
lean_inc(v_a_5087_);
lean_inc_ref(v_a_5086_);
lean_inc(v_a_5085_);
lean_inc_ref(v_a_5084_);
lean_inc(v_a_5083_);
lean_inc_ref(v_a_5082_);
lean_inc(v_a_5081_);
lean_inc_ref(v_a_5080_);
lean_inc(v_a_5079_);
lean_inc(v_a_5078_);
lean_inc_ref(v_a_5077_);
v___x_5244_ = lean_apply_12(v_run_x27_5145_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, lean_box(0));
return v___x_5244_;
}
else
{
goto v___jp_5188_;
}
}
else
{
goto v___jp_5188_;
}
v___jp_5157_:
{
lean_object* v___x_5161_; double v___x_5162_; double v___x_5163_; double v___x_5164_; double v___x_5165_; double v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5170_; 
v___x_5161_ = lean_io_mono_nanos_now();
v___x_5162_ = lean_float_of_nat(v___y_5158_);
v___x_5163_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_5164_ = lean_float_div(v___x_5162_, v___x_5163_);
v___x_5165_ = lean_float_of_nat(v___x_5161_);
v___x_5166_ = lean_float_div(v___x_5165_, v___x_5163_);
v___x_5167_ = lean_box_float(v___x_5164_);
v___x_5168_ = lean_box_float(v___x_5166_);
if (v_isShared_5148_ == 0)
{
lean_ctor_set(v___x_5147_, 1, v___x_5168_);
lean_ctor_set(v___x_5147_, 0, v___x_5167_);
v___x_5170_ = v___x_5147_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5167_);
lean_ctor_set(v_reuseFailAlloc_5174_, 1, v___x_5168_);
v___x_5170_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
lean_object* v___x_5171_; lean_object* v___x_29258__overap_5172_; lean_object* v___x_5173_; 
v___x_5171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5171_, 0, v_a_5160_);
lean_ctor_set(v___x_5171_, 1, v___x_5170_);
lean_inc_ref(v_toMonadRef_5138_);
v___x_29258__overap_5172_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5135_, v___x_5136_, v_toMonadRef_5138_, v___f_5151_, lean_box(0), v___x_5139_, v___f_5152_, v___x_5153_, v_hasTrace_5141_, v___x_5154_, v_options_5140_, v___x_5156_, v___y_5159_, v___f_5150_, v___x_5171_);
lean_inc(v_a_5087_);
lean_inc_ref(v_a_5086_);
lean_inc(v_a_5085_);
lean_inc_ref(v_a_5084_);
lean_inc(v_a_5083_);
lean_inc_ref(v_a_5082_);
lean_inc(v_a_5081_);
lean_inc_ref(v_a_5080_);
lean_inc(v_a_5079_);
lean_inc(v_a_5078_);
lean_inc_ref(v_a_5077_);
v___x_5173_ = lean_apply_12(v___x_29258__overap_5172_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, lean_box(0));
return v___x_5173_;
}
}
v___jp_5175_:
{
lean_object* v___x_5179_; double v___x_5180_; double v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_29279__overap_5186_; lean_object* v___x_5187_; 
v___x_5179_ = lean_io_get_num_heartbeats();
v___x_5180_ = lean_float_of_nat(v___y_5176_);
v___x_5181_ = lean_float_of_nat(v___x_5179_);
v___x_5182_ = lean_box_float(v___x_5180_);
v___x_5183_ = lean_box_float(v___x_5181_);
v___x_5184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5184_, 0, v___x_5182_);
lean_ctor_set(v___x_5184_, 1, v___x_5183_);
v___x_5185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5185_, 0, v_a_5178_);
lean_ctor_set(v___x_5185_, 1, v___x_5184_);
lean_inc_ref(v_toMonadRef_5138_);
v___x_29279__overap_5186_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_5135_, v___x_5136_, v_toMonadRef_5138_, v___f_5151_, lean_box(0), v___x_5139_, v___f_5152_, v___x_5153_, v_hasTrace_5141_, v___x_5154_, v_options_5140_, v___x_5156_, v___y_5177_, v___f_5150_, v___x_5185_);
lean_inc(v_a_5087_);
lean_inc_ref(v_a_5086_);
lean_inc(v_a_5085_);
lean_inc_ref(v_a_5084_);
lean_inc(v_a_5083_);
lean_inc_ref(v_a_5082_);
lean_inc(v_a_5081_);
lean_inc_ref(v_a_5080_);
lean_inc(v_a_5079_);
lean_inc(v_a_5078_);
lean_inc_ref(v_a_5077_);
v___x_5187_ = lean_apply_12(v___x_29279__overap_5186_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, lean_box(0));
return v___x_5187_;
}
v___jp_5188_:
{
lean_object* v___x_29235__overap_5189_; lean_object* v___x_5190_; 
lean_inc_ref(v___x_5135_);
v___x_29235__overap_5189_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_5135_, v___x_5136_);
lean_inc(v_a_5087_);
lean_inc_ref(v_a_5086_);
lean_inc(v_a_5085_);
lean_inc_ref(v_a_5084_);
lean_inc(v_a_5083_);
lean_inc_ref(v_a_5082_);
lean_inc(v_a_5081_);
lean_inc_ref(v_a_5080_);
lean_inc(v_a_5079_);
lean_inc(v_a_5078_);
lean_inc_ref(v_a_5077_);
v___x_5190_ = lean_apply_12(v___x_29235__overap_5189_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, lean_box(0));
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_object* v_a_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; uint8_t v___x_5195_; 
v_a_5191_ = lean_ctor_get(v___x_5190_, 0);
lean_inc(v_a_5191_);
lean_dec_ref_known(v___x_5190_, 1);
v___x_5192_ = l_Lean_KVMap_instValueBool;
v___x_5193_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5194_ = l_Lean_Option_get___redArg(v___x_5192_, v_options_5140_, v___x_5193_);
v___x_5195_ = lean_unbox(v___x_5194_);
lean_dec(v___x_5194_);
if (v___x_5195_ == 0)
{
lean_object* v___x_5196_; lean_object* v___x_5197_; 
v___x_5196_ = lean_io_mono_nanos_now();
lean_inc(v_a_5087_);
lean_inc_ref(v_a_5086_);
lean_inc(v_a_5085_);
lean_inc_ref(v_a_5084_);
lean_inc(v_a_5083_);
lean_inc_ref(v_a_5082_);
lean_inc(v_a_5081_);
lean_inc_ref(v_a_5080_);
lean_inc(v_a_5079_);
lean_inc(v_a_5078_);
lean_inc_ref(v_a_5077_);
v___x_5197_ = lean_apply_12(v_run_x27_5145_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, lean_box(0));
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v_a_5198_; lean_object* v___x_5200_; uint8_t v_isShared_5201_; uint8_t v_isSharedCheck_5205_; 
v_a_5198_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5205_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5200_ = v___x_5197_;
v_isShared_5201_ = v_isSharedCheck_5205_;
goto v_resetjp_5199_;
}
else
{
lean_inc(v_a_5198_);
lean_dec(v___x_5197_);
v___x_5200_ = lean_box(0);
v_isShared_5201_ = v_isSharedCheck_5205_;
goto v_resetjp_5199_;
}
v_resetjp_5199_:
{
lean_object* v___x_5203_; 
if (v_isShared_5201_ == 0)
{
lean_ctor_set_tag(v___x_5200_, 1);
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
v___y_5158_ = v___x_5196_;
v___y_5159_ = v_a_5191_;
v_a_5160_ = v___x_5203_;
goto v___jp_5157_;
}
}
}
else
{
lean_object* v_a_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5213_; 
v_a_5206_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5213_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5213_ == 0)
{
v___x_5208_ = v___x_5197_;
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_a_5206_);
lean_dec(v___x_5197_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
lean_object* v___x_5211_; 
if (v_isShared_5209_ == 0)
{
lean_ctor_set_tag(v___x_5208_, 0);
v___x_5211_ = v___x_5208_;
goto v_reusejp_5210_;
}
else
{
lean_object* v_reuseFailAlloc_5212_; 
v_reuseFailAlloc_5212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5212_, 0, v_a_5206_);
v___x_5211_ = v_reuseFailAlloc_5212_;
goto v_reusejp_5210_;
}
v_reusejp_5210_:
{
v___y_5158_ = v___x_5196_;
v___y_5159_ = v_a_5191_;
v_a_5160_ = v___x_5211_;
goto v___jp_5157_;
}
}
}
}
else
{
lean_object* v___x_5214_; lean_object* v___x_5215_; 
lean_del_object(v___x_5147_);
v___x_5214_ = lean_io_get_num_heartbeats();
lean_inc(v_a_5087_);
lean_inc_ref(v_a_5086_);
lean_inc(v_a_5085_);
lean_inc_ref(v_a_5084_);
lean_inc(v_a_5083_);
lean_inc_ref(v_a_5082_);
lean_inc(v_a_5081_);
lean_inc_ref(v_a_5080_);
lean_inc(v_a_5079_);
lean_inc(v_a_5078_);
lean_inc_ref(v_a_5077_);
v___x_5215_ = lean_apply_12(v_run_x27_5145_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, lean_box(0));
if (lean_obj_tag(v___x_5215_) == 0)
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5223_; 
v_a_5216_ = lean_ctor_get(v___x_5215_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5215_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5218_ = v___x_5215_;
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_5215_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
lean_ctor_set_tag(v___x_5218_, 1);
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_a_5216_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
v___y_5176_ = v___x_5214_;
v___y_5177_ = v_a_5191_;
v_a_5178_ = v___x_5221_;
goto v___jp_5175_;
}
}
}
else
{
lean_object* v_a_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5231_; 
v_a_5224_ = lean_ctor_get(v___x_5215_, 0);
v_isSharedCheck_5231_ = !lean_is_exclusive(v___x_5215_);
if (v_isSharedCheck_5231_ == 0)
{
v___x_5226_ = v___x_5215_;
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_a_5224_);
lean_dec(v___x_5215_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5231_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v___x_5229_; 
if (v_isShared_5227_ == 0)
{
lean_ctor_set_tag(v___x_5226_, 0);
v___x_5229_ = v___x_5226_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_a_5224_);
v___x_5229_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
v___y_5176_ = v___x_5214_;
v___y_5177_ = v_a_5191_;
v_a_5178_ = v___x_5229_;
goto v___jp_5175_;
}
}
}
}
}
else
{
lean_object* v_a_5232_; lean_object* v___x_5234_; uint8_t v_isShared_5235_; uint8_t v_isSharedCheck_5239_; 
lean_dec_ref(v___f_5150_);
lean_del_object(v___x_5147_);
lean_dec_ref(v_run_x27_5145_);
lean_dec_ref(v___x_5135_);
v_a_5232_ = lean_ctor_get(v___x_5190_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5190_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5234_ = v___x_5190_;
v_isShared_5235_ = v_isSharedCheck_5239_;
goto v_resetjp_5233_;
}
else
{
lean_inc(v_a_5232_);
lean_dec(v___x_5190_);
v___x_5234_ = lean_box(0);
v_isShared_5235_ = v_isSharedCheck_5239_;
goto v_resetjp_5233_;
}
v_resetjp_5233_:
{
lean_object* v___x_5237_; 
if (v_isShared_5235_ == 0)
{
v___x_5237_ = v___x_5234_;
goto v_reusejp_5236_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v_a_5232_);
v___x_5237_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5236_;
}
v_reusejp_5236_:
{
return v___x_5237_;
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_){
_start:
{
lean_object* v_res_5265_; 
v_res_5265_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
lean_dec(v_a_5259_);
lean_dec_ref(v_a_5258_);
lean_dec(v_a_5257_);
lean_dec_ref(v_a_5256_);
lean_dec(v_a_5255_);
lean_dec(v_a_5254_);
lean_dec_ref(v_a_5253_);
return v_res_5265_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; 
v___x_5266_ = lean_unsigned_to_nat(32u);
v___x_5267_ = lean_mk_empty_array_with_capacity(v___x_5266_);
v___x_5268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5268_, 0, v___x_5267_);
return v___x_5268_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; 
v___x_5269_ = ((size_t)5ULL);
v___x_5270_ = lean_unsigned_to_nat(0u);
v___x_5271_ = lean_unsigned_to_nat(32u);
v___x_5272_ = lean_mk_empty_array_with_capacity(v___x_5271_);
v___x_5273_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_5274_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5274_, 0, v___x_5273_);
lean_ctor_set(v___x_5274_, 1, v___x_5272_);
lean_ctor_set(v___x_5274_, 2, v___x_5270_);
lean_ctor_set(v___x_5274_, 3, v___x_5270_);
lean_ctor_set_usize(v___x_5274_, 4, v___x_5269_);
return v___x_5274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_5275_){
_start:
{
lean_object* v___x_5277_; lean_object* v_traceState_5278_; lean_object* v_traces_5279_; lean_object* v___x_5280_; lean_object* v_traceState_5281_; lean_object* v_env_5282_; lean_object* v_nextMacroScope_5283_; lean_object* v_ngen_5284_; lean_object* v_auxDeclNGen_5285_; lean_object* v_cache_5286_; lean_object* v_messages_5287_; lean_object* v_infoState_5288_; lean_object* v_snapshotTasks_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5308_; 
v___x_5277_ = lean_st_ref_get(v___y_5275_);
v_traceState_5278_ = lean_ctor_get(v___x_5277_, 4);
lean_inc_ref(v_traceState_5278_);
lean_dec(v___x_5277_);
v_traces_5279_ = lean_ctor_get(v_traceState_5278_, 0);
lean_inc_ref(v_traces_5279_);
lean_dec_ref(v_traceState_5278_);
v___x_5280_ = lean_st_ref_take(v___y_5275_);
v_traceState_5281_ = lean_ctor_get(v___x_5280_, 4);
v_env_5282_ = lean_ctor_get(v___x_5280_, 0);
v_nextMacroScope_5283_ = lean_ctor_get(v___x_5280_, 1);
v_ngen_5284_ = lean_ctor_get(v___x_5280_, 2);
v_auxDeclNGen_5285_ = lean_ctor_get(v___x_5280_, 3);
v_cache_5286_ = lean_ctor_get(v___x_5280_, 5);
v_messages_5287_ = lean_ctor_get(v___x_5280_, 6);
v_infoState_5288_ = lean_ctor_get(v___x_5280_, 7);
v_snapshotTasks_5289_ = lean_ctor_get(v___x_5280_, 8);
v_isSharedCheck_5308_ = !lean_is_exclusive(v___x_5280_);
if (v_isSharedCheck_5308_ == 0)
{
v___x_5291_ = v___x_5280_;
v_isShared_5292_ = v_isSharedCheck_5308_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_snapshotTasks_5289_);
lean_inc(v_infoState_5288_);
lean_inc(v_messages_5287_);
lean_inc(v_cache_5286_);
lean_inc(v_traceState_5281_);
lean_inc(v_auxDeclNGen_5285_);
lean_inc(v_ngen_5284_);
lean_inc(v_nextMacroScope_5283_);
lean_inc(v_env_5282_);
lean_dec(v___x_5280_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5308_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
uint64_t v_tid_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5306_; 
v_tid_5293_ = lean_ctor_get_uint64(v_traceState_5281_, sizeof(void*)*1);
v_isSharedCheck_5306_ = !lean_is_exclusive(v_traceState_5281_);
if (v_isSharedCheck_5306_ == 0)
{
lean_object* v_unused_5307_; 
v_unused_5307_ = lean_ctor_get(v_traceState_5281_, 0);
lean_dec(v_unused_5307_);
v___x_5295_ = v_traceState_5281_;
v_isShared_5296_ = v_isSharedCheck_5306_;
goto v_resetjp_5294_;
}
else
{
lean_dec(v_traceState_5281_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5306_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5297_; lean_object* v___x_5299_; 
v___x_5297_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_5296_ == 0)
{
lean_ctor_set(v___x_5295_, 0, v___x_5297_);
v___x_5299_ = v___x_5295_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v___x_5297_);
lean_ctor_set_uint64(v_reuseFailAlloc_5305_, sizeof(void*)*1, v_tid_5293_);
v___x_5299_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5301_; 
if (v_isShared_5292_ == 0)
{
lean_ctor_set(v___x_5291_, 4, v___x_5299_);
v___x_5301_ = v___x_5291_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_env_5282_);
lean_ctor_set(v_reuseFailAlloc_5304_, 1, v_nextMacroScope_5283_);
lean_ctor_set(v_reuseFailAlloc_5304_, 2, v_ngen_5284_);
lean_ctor_set(v_reuseFailAlloc_5304_, 3, v_auxDeclNGen_5285_);
lean_ctor_set(v_reuseFailAlloc_5304_, 4, v___x_5299_);
lean_ctor_set(v_reuseFailAlloc_5304_, 5, v_cache_5286_);
lean_ctor_set(v_reuseFailAlloc_5304_, 6, v_messages_5287_);
lean_ctor_set(v_reuseFailAlloc_5304_, 7, v_infoState_5288_);
lean_ctor_set(v_reuseFailAlloc_5304_, 8, v_snapshotTasks_5289_);
v___x_5301_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
lean_object* v___x_5302_; lean_object* v___x_5303_; 
v___x_5302_ = lean_st_ref_set(v___y_5275_, v___x_5301_);
v___x_5303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5303_, 0, v_traces_5279_);
return v___x_5303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_5309_, lean_object* v___y_5310_){
_start:
{
lean_object* v_res_5311_; 
v_res_5311_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_5309_);
lean_dec(v___y_5309_);
return v_res_5311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_){
_start:
{
lean_object* v___x_5324_; 
v___x_5324_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_5322_);
return v___x_5324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_){
_start:
{
lean_object* v_res_5337_; 
v_res_5337_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5334_);
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
lean_dec(v___y_5331_);
lean_dec_ref(v___y_5330_);
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
lean_dec(v___y_5327_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
return v_res_5337_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_5338_, lean_object* v_opt_5339_){
_start:
{
lean_object* v_name_5340_; lean_object* v_defValue_5341_; lean_object* v_map_5342_; lean_object* v___x_5343_; 
v_name_5340_ = lean_ctor_get(v_opt_5339_, 0);
v_defValue_5341_ = lean_ctor_get(v_opt_5339_, 1);
v_map_5342_ = lean_ctor_get(v_opts_5338_, 0);
v___x_5343_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5342_, v_name_5340_);
if (lean_obj_tag(v___x_5343_) == 0)
{
uint8_t v___x_5344_; 
v___x_5344_ = lean_unbox(v_defValue_5341_);
return v___x_5344_;
}
else
{
lean_object* v_val_5345_; 
v_val_5345_ = lean_ctor_get(v___x_5343_, 0);
lean_inc(v_val_5345_);
lean_dec_ref_known(v___x_5343_, 1);
if (lean_obj_tag(v_val_5345_) == 1)
{
uint8_t v_v_5346_; 
v_v_5346_ = lean_ctor_get_uint8(v_val_5345_, 0);
lean_dec_ref_known(v_val_5345_, 0);
return v_v_5346_;
}
else
{
uint8_t v___x_5347_; 
lean_dec(v_val_5345_);
v___x_5347_ = lean_unbox(v_defValue_5341_);
return v___x_5347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_5348_, lean_object* v_opt_5349_){
_start:
{
uint8_t v_res_5350_; lean_object* v_r_5351_; 
v_res_5350_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_5348_, v_opt_5349_);
lean_dec_ref(v_opt_5349_);
lean_dec_ref(v_opts_5348_);
v_r_5351_ = lean_box(v_res_5350_);
return v_r_5351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_5352_, lean_object* v_msg_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_){
_start:
{
lean_object* v_ref_5359_; lean_object* v___x_5360_; lean_object* v_a_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5405_; 
v_ref_5359_ = lean_ctor_get(v___y_5356_, 5);
v___x_5360_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_);
v_a_5361_ = lean_ctor_get(v___x_5360_, 0);
v_isSharedCheck_5405_ = !lean_is_exclusive(v___x_5360_);
if (v_isSharedCheck_5405_ == 0)
{
v___x_5363_ = v___x_5360_;
v_isShared_5364_ = v_isSharedCheck_5405_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_a_5361_);
lean_dec(v___x_5360_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5405_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v___x_5365_; lean_object* v_traceState_5366_; lean_object* v_env_5367_; lean_object* v_nextMacroScope_5368_; lean_object* v_ngen_5369_; lean_object* v_auxDeclNGen_5370_; lean_object* v_cache_5371_; lean_object* v_messages_5372_; lean_object* v_infoState_5373_; lean_object* v_snapshotTasks_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5404_; 
v___x_5365_ = lean_st_ref_take(v___y_5357_);
v_traceState_5366_ = lean_ctor_get(v___x_5365_, 4);
v_env_5367_ = lean_ctor_get(v___x_5365_, 0);
v_nextMacroScope_5368_ = lean_ctor_get(v___x_5365_, 1);
v_ngen_5369_ = lean_ctor_get(v___x_5365_, 2);
v_auxDeclNGen_5370_ = lean_ctor_get(v___x_5365_, 3);
v_cache_5371_ = lean_ctor_get(v___x_5365_, 5);
v_messages_5372_ = lean_ctor_get(v___x_5365_, 6);
v_infoState_5373_ = lean_ctor_get(v___x_5365_, 7);
v_snapshotTasks_5374_ = lean_ctor_get(v___x_5365_, 8);
v_isSharedCheck_5404_ = !lean_is_exclusive(v___x_5365_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5376_ = v___x_5365_;
v_isShared_5377_ = v_isSharedCheck_5404_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_snapshotTasks_5374_);
lean_inc(v_infoState_5373_);
lean_inc(v_messages_5372_);
lean_inc(v_cache_5371_);
lean_inc(v_traceState_5366_);
lean_inc(v_auxDeclNGen_5370_);
lean_inc(v_ngen_5369_);
lean_inc(v_nextMacroScope_5368_);
lean_inc(v_env_5367_);
lean_dec(v___x_5365_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5404_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
uint64_t v_tid_5378_; lean_object* v_traces_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5403_; 
v_tid_5378_ = lean_ctor_get_uint64(v_traceState_5366_, sizeof(void*)*1);
v_traces_5379_ = lean_ctor_get(v_traceState_5366_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v_traceState_5366_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5381_ = v_traceState_5366_;
v_isShared_5382_ = v_isSharedCheck_5403_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_traces_5379_);
lean_dec(v_traceState_5366_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5403_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v___x_5383_; double v___x_5384_; uint8_t v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5393_; 
v___x_5383_ = lean_box(0);
v___x_5384_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5385_ = 0;
v___x_5386_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5387_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5387_, 0, v_cls_5352_);
lean_ctor_set(v___x_5387_, 1, v___x_5383_);
lean_ctor_set(v___x_5387_, 2, v___x_5386_);
lean_ctor_set_float(v___x_5387_, sizeof(void*)*3, v___x_5384_);
lean_ctor_set_float(v___x_5387_, sizeof(void*)*3 + 8, v___x_5384_);
lean_ctor_set_uint8(v___x_5387_, sizeof(void*)*3 + 16, v___x_5385_);
v___x_5388_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5389_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5389_, 0, v___x_5387_);
lean_ctor_set(v___x_5389_, 1, v_a_5361_);
lean_ctor_set(v___x_5389_, 2, v___x_5388_);
lean_inc(v_ref_5359_);
v___x_5390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5390_, 0, v_ref_5359_);
lean_ctor_set(v___x_5390_, 1, v___x_5389_);
v___x_5391_ = l_Lean_PersistentArray_push___redArg(v_traces_5379_, v___x_5390_);
if (v_isShared_5382_ == 0)
{
lean_ctor_set(v___x_5381_, 0, v___x_5391_);
v___x_5393_ = v___x_5381_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5391_);
lean_ctor_set_uint64(v_reuseFailAlloc_5402_, sizeof(void*)*1, v_tid_5378_);
v___x_5393_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
lean_object* v___x_5395_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 4, v___x_5393_);
v___x_5395_ = v___x_5376_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v_env_5367_);
lean_ctor_set(v_reuseFailAlloc_5401_, 1, v_nextMacroScope_5368_);
lean_ctor_set(v_reuseFailAlloc_5401_, 2, v_ngen_5369_);
lean_ctor_set(v_reuseFailAlloc_5401_, 3, v_auxDeclNGen_5370_);
lean_ctor_set(v_reuseFailAlloc_5401_, 4, v___x_5393_);
lean_ctor_set(v_reuseFailAlloc_5401_, 5, v_cache_5371_);
lean_ctor_set(v_reuseFailAlloc_5401_, 6, v_messages_5372_);
lean_ctor_set(v_reuseFailAlloc_5401_, 7, v_infoState_5373_);
lean_ctor_set(v_reuseFailAlloc_5401_, 8, v_snapshotTasks_5374_);
v___x_5395_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5399_; 
v___x_5396_ = lean_st_ref_set(v___y_5357_, v___x_5395_);
v___x_5397_ = lean_box(0);
if (v_isShared_5364_ == 0)
{
lean_ctor_set(v___x_5363_, 0, v___x_5397_);
v___x_5399_ = v___x_5363_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v___x_5397_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object* v_cls_5406_, lean_object* v_msg_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_){
_start:
{
lean_object* v_res_5413_; 
v_res_5413_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_5406_, v_msg_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_);
lean_dec(v___y_5411_);
lean_dec_ref(v___y_5410_);
lean_dec(v___y_5409_);
lean_dec_ref(v___y_5408_);
return v_res_5413_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object* v_e_5414_){
_start:
{
if (lean_obj_tag(v_e_5414_) == 0)
{
uint8_t v___x_5415_; 
v___x_5415_ = 2;
return v___x_5415_;
}
else
{
lean_object* v_a_5416_; uint8_t v___x_5417_; 
v_a_5416_ = lean_ctor_get(v_e_5414_, 0);
v___x_5417_ = lean_unbox(v_a_5416_);
if (v___x_5417_ == 0)
{
uint8_t v___x_5418_; 
v___x_5418_ = 1;
return v___x_5418_;
}
else
{
uint8_t v___x_5419_; 
v___x_5419_ = 0;
return v___x_5419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object* v_e_5420_){
_start:
{
uint8_t v_res_5421_; lean_object* v_r_5422_; 
v_res_5421_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_5420_);
lean_dec_ref(v_e_5420_);
v_r_5422_ = lean_box(v_res_5421_);
return v_r_5422_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object* v_x_5423_){
_start:
{
if (lean_obj_tag(v_x_5423_) == 0)
{
lean_object* v_a_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5432_; 
v_a_5425_ = lean_ctor_get(v_x_5423_, 0);
v_isSharedCheck_5432_ = !lean_is_exclusive(v_x_5423_);
if (v_isSharedCheck_5432_ == 0)
{
v___x_5427_ = v_x_5423_;
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_a_5425_);
lean_dec(v_x_5423_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
lean_object* v___x_5430_; 
if (v_isShared_5428_ == 0)
{
lean_ctor_set_tag(v___x_5427_, 1);
v___x_5430_ = v___x_5427_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_a_5425_);
v___x_5430_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
return v___x_5430_;
}
}
}
else
{
lean_object* v_a_5433_; lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5440_; 
v_a_5433_ = lean_ctor_get(v_x_5423_, 0);
v_isSharedCheck_5440_ = !lean_is_exclusive(v_x_5423_);
if (v_isSharedCheck_5440_ == 0)
{
v___x_5435_ = v_x_5423_;
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
else
{
lean_inc(v_a_5433_);
lean_dec(v_x_5423_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
lean_object* v___x_5438_; 
if (v_isShared_5436_ == 0)
{
lean_ctor_set_tag(v___x_5435_, 0);
v___x_5438_ = v___x_5435_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_a_5433_);
v___x_5438_ = v_reuseFailAlloc_5439_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
return v___x_5438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_5441_, lean_object* v___y_5442_){
_start:
{
lean_object* v_res_5443_; 
v_res_5443_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_5441_);
return v_res_5443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object* v_opts_5444_, lean_object* v_opt_5445_){
_start:
{
lean_object* v_name_5446_; lean_object* v_defValue_5447_; lean_object* v_map_5448_; lean_object* v___x_5449_; 
v_name_5446_ = lean_ctor_get(v_opt_5445_, 0);
v_defValue_5447_ = lean_ctor_get(v_opt_5445_, 1);
v_map_5448_ = lean_ctor_get(v_opts_5444_, 0);
v___x_5449_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5448_, v_name_5446_);
if (lean_obj_tag(v___x_5449_) == 0)
{
lean_inc(v_defValue_5447_);
return v_defValue_5447_;
}
else
{
lean_object* v_val_5450_; 
v_val_5450_ = lean_ctor_get(v___x_5449_, 0);
lean_inc(v_val_5450_);
lean_dec_ref_known(v___x_5449_, 1);
if (lean_obj_tag(v_val_5450_) == 3)
{
lean_object* v_v_5451_; 
v_v_5451_ = lean_ctor_get(v_val_5450_, 0);
lean_inc(v_v_5451_);
lean_dec_ref_known(v_val_5450_, 1);
return v_v_5451_;
}
else
{
lean_dec(v_val_5450_);
lean_inc(v_defValue_5447_);
return v_defValue_5447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object* v_opts_5452_, lean_object* v_opt_5453_){
_start:
{
lean_object* v_res_5454_; 
v_res_5454_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_5452_, v_opt_5453_);
lean_dec_ref(v_opt_5453_);
lean_dec_ref(v_opts_5452_);
return v_res_5454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t v_sz_5455_, size_t v_i_5456_, lean_object* v_bs_5457_){
_start:
{
uint8_t v___x_5458_; 
v___x_5458_ = lean_usize_dec_lt(v_i_5456_, v_sz_5455_);
if (v___x_5458_ == 0)
{
return v_bs_5457_;
}
else
{
lean_object* v_v_5459_; lean_object* v_msg_5460_; lean_object* v___x_5461_; lean_object* v_bs_x27_5462_; size_t v___x_5463_; size_t v___x_5464_; lean_object* v___x_5465_; 
v_v_5459_ = lean_array_uget_borrowed(v_bs_5457_, v_i_5456_);
v_msg_5460_ = lean_ctor_get(v_v_5459_, 1);
lean_inc_ref(v_msg_5460_);
v___x_5461_ = lean_unsigned_to_nat(0u);
v_bs_x27_5462_ = lean_array_uset(v_bs_5457_, v_i_5456_, v___x_5461_);
v___x_5463_ = ((size_t)1ULL);
v___x_5464_ = lean_usize_add(v_i_5456_, v___x_5463_);
v___x_5465_ = lean_array_uset(v_bs_x27_5462_, v_i_5456_, v_msg_5460_);
v_i_5456_ = v___x_5464_;
v_bs_5457_ = v___x_5465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_5467_, lean_object* v_i_5468_, lean_object* v_bs_5469_){
_start:
{
size_t v_sz_boxed_5470_; size_t v_i_boxed_5471_; lean_object* v_res_5472_; 
v_sz_boxed_5470_ = lean_unbox_usize(v_sz_5467_);
lean_dec(v_sz_5467_);
v_i_boxed_5471_ = lean_unbox_usize(v_i_5468_);
lean_dec(v_i_5468_);
v_res_5472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_boxed_5470_, v_i_boxed_5471_, v_bs_5469_);
return v_res_5472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object* v_oldTraces_5473_, lean_object* v_data_5474_, lean_object* v_ref_5475_, lean_object* v_msg_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_){
_start:
{
lean_object* v_fileName_5482_; lean_object* v_fileMap_5483_; lean_object* v_options_5484_; lean_object* v_currRecDepth_5485_; lean_object* v_maxRecDepth_5486_; lean_object* v_ref_5487_; lean_object* v_currNamespace_5488_; lean_object* v_openDecls_5489_; lean_object* v_initHeartbeats_5490_; lean_object* v_maxHeartbeats_5491_; lean_object* v_quotContext_5492_; lean_object* v_currMacroScope_5493_; uint8_t v_diag_5494_; lean_object* v_cancelTk_x3f_5495_; uint8_t v_suppressElabErrors_5496_; lean_object* v_inheritedTraceOptions_5497_; lean_object* v___x_5498_; lean_object* v_traceState_5499_; lean_object* v_traces_5500_; lean_object* v_ref_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; size_t v_sz_5504_; size_t v___x_5505_; lean_object* v___x_5506_; lean_object* v_msg_5507_; lean_object* v___x_5508_; lean_object* v_a_5509_; lean_object* v___x_5511_; uint8_t v_isShared_5512_; uint8_t v_isSharedCheck_5546_; 
v_fileName_5482_ = lean_ctor_get(v___y_5479_, 0);
v_fileMap_5483_ = lean_ctor_get(v___y_5479_, 1);
v_options_5484_ = lean_ctor_get(v___y_5479_, 2);
v_currRecDepth_5485_ = lean_ctor_get(v___y_5479_, 3);
v_maxRecDepth_5486_ = lean_ctor_get(v___y_5479_, 4);
v_ref_5487_ = lean_ctor_get(v___y_5479_, 5);
v_currNamespace_5488_ = lean_ctor_get(v___y_5479_, 6);
v_openDecls_5489_ = lean_ctor_get(v___y_5479_, 7);
v_initHeartbeats_5490_ = lean_ctor_get(v___y_5479_, 8);
v_maxHeartbeats_5491_ = lean_ctor_get(v___y_5479_, 9);
v_quotContext_5492_ = lean_ctor_get(v___y_5479_, 10);
v_currMacroScope_5493_ = lean_ctor_get(v___y_5479_, 11);
v_diag_5494_ = lean_ctor_get_uint8(v___y_5479_, sizeof(void*)*14);
v_cancelTk_x3f_5495_ = lean_ctor_get(v___y_5479_, 12);
v_suppressElabErrors_5496_ = lean_ctor_get_uint8(v___y_5479_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5497_ = lean_ctor_get(v___y_5479_, 13);
v___x_5498_ = lean_st_ref_get(v___y_5480_);
v_traceState_5499_ = lean_ctor_get(v___x_5498_, 4);
lean_inc_ref(v_traceState_5499_);
lean_dec(v___x_5498_);
v_traces_5500_ = lean_ctor_get(v_traceState_5499_, 0);
lean_inc_ref(v_traces_5500_);
lean_dec_ref(v_traceState_5499_);
v_ref_5501_ = l_Lean_replaceRef(v_ref_5475_, v_ref_5487_);
lean_inc_ref(v_inheritedTraceOptions_5497_);
lean_inc(v_cancelTk_x3f_5495_);
lean_inc(v_currMacroScope_5493_);
lean_inc(v_quotContext_5492_);
lean_inc(v_maxHeartbeats_5491_);
lean_inc(v_initHeartbeats_5490_);
lean_inc(v_openDecls_5489_);
lean_inc(v_currNamespace_5488_);
lean_inc(v_maxRecDepth_5486_);
lean_inc(v_currRecDepth_5485_);
lean_inc_ref(v_options_5484_);
lean_inc_ref(v_fileMap_5483_);
lean_inc_ref(v_fileName_5482_);
v___x_5502_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5502_, 0, v_fileName_5482_);
lean_ctor_set(v___x_5502_, 1, v_fileMap_5483_);
lean_ctor_set(v___x_5502_, 2, v_options_5484_);
lean_ctor_set(v___x_5502_, 3, v_currRecDepth_5485_);
lean_ctor_set(v___x_5502_, 4, v_maxRecDepth_5486_);
lean_ctor_set(v___x_5502_, 5, v_ref_5501_);
lean_ctor_set(v___x_5502_, 6, v_currNamespace_5488_);
lean_ctor_set(v___x_5502_, 7, v_openDecls_5489_);
lean_ctor_set(v___x_5502_, 8, v_initHeartbeats_5490_);
lean_ctor_set(v___x_5502_, 9, v_maxHeartbeats_5491_);
lean_ctor_set(v___x_5502_, 10, v_quotContext_5492_);
lean_ctor_set(v___x_5502_, 11, v_currMacroScope_5493_);
lean_ctor_set(v___x_5502_, 12, v_cancelTk_x3f_5495_);
lean_ctor_set(v___x_5502_, 13, v_inheritedTraceOptions_5497_);
lean_ctor_set_uint8(v___x_5502_, sizeof(void*)*14, v_diag_5494_);
lean_ctor_set_uint8(v___x_5502_, sizeof(void*)*14 + 1, v_suppressElabErrors_5496_);
v___x_5503_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5500_);
lean_dec_ref(v_traces_5500_);
v_sz_5504_ = lean_array_size(v___x_5503_);
v___x_5505_ = ((size_t)0ULL);
v___x_5506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_5504_, v___x_5505_, v___x_5503_);
v_msg_5507_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5507_, 0, v_data_5474_);
lean_ctor_set(v_msg_5507_, 1, v_msg_5476_);
lean_ctor_set(v_msg_5507_, 2, v___x_5506_);
v___x_5508_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5507_, v___y_5477_, v___y_5478_, v___x_5502_, v___y_5480_);
lean_dec_ref_known(v___x_5502_, 14);
v_a_5509_ = lean_ctor_get(v___x_5508_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5508_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5511_ = v___x_5508_;
v_isShared_5512_ = v_isSharedCheck_5546_;
goto v_resetjp_5510_;
}
else
{
lean_inc(v_a_5509_);
lean_dec(v___x_5508_);
v___x_5511_ = lean_box(0);
v_isShared_5512_ = v_isSharedCheck_5546_;
goto v_resetjp_5510_;
}
v_resetjp_5510_:
{
lean_object* v___x_5513_; lean_object* v_traceState_5514_; lean_object* v_env_5515_; lean_object* v_nextMacroScope_5516_; lean_object* v_ngen_5517_; lean_object* v_auxDeclNGen_5518_; lean_object* v_cache_5519_; lean_object* v_messages_5520_; lean_object* v_infoState_5521_; lean_object* v_snapshotTasks_5522_; lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5545_; 
v___x_5513_ = lean_st_ref_take(v___y_5480_);
v_traceState_5514_ = lean_ctor_get(v___x_5513_, 4);
v_env_5515_ = lean_ctor_get(v___x_5513_, 0);
v_nextMacroScope_5516_ = lean_ctor_get(v___x_5513_, 1);
v_ngen_5517_ = lean_ctor_get(v___x_5513_, 2);
v_auxDeclNGen_5518_ = lean_ctor_get(v___x_5513_, 3);
v_cache_5519_ = lean_ctor_get(v___x_5513_, 5);
v_messages_5520_ = lean_ctor_get(v___x_5513_, 6);
v_infoState_5521_ = lean_ctor_get(v___x_5513_, 7);
v_snapshotTasks_5522_ = lean_ctor_get(v___x_5513_, 8);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5513_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5524_ = v___x_5513_;
v_isShared_5525_ = v_isSharedCheck_5545_;
goto v_resetjp_5523_;
}
else
{
lean_inc(v_snapshotTasks_5522_);
lean_inc(v_infoState_5521_);
lean_inc(v_messages_5520_);
lean_inc(v_cache_5519_);
lean_inc(v_traceState_5514_);
lean_inc(v_auxDeclNGen_5518_);
lean_inc(v_ngen_5517_);
lean_inc(v_nextMacroScope_5516_);
lean_inc(v_env_5515_);
lean_dec(v___x_5513_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5545_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
uint64_t v_tid_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5543_; 
v_tid_5526_ = lean_ctor_get_uint64(v_traceState_5514_, sizeof(void*)*1);
v_isSharedCheck_5543_ = !lean_is_exclusive(v_traceState_5514_);
if (v_isSharedCheck_5543_ == 0)
{
lean_object* v_unused_5544_; 
v_unused_5544_ = lean_ctor_get(v_traceState_5514_, 0);
lean_dec(v_unused_5544_);
v___x_5528_ = v_traceState_5514_;
v_isShared_5529_ = v_isSharedCheck_5543_;
goto v_resetjp_5527_;
}
else
{
lean_dec(v_traceState_5514_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5543_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5533_; 
v___x_5530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5530_, 0, v_ref_5475_);
lean_ctor_set(v___x_5530_, 1, v_a_5509_);
v___x_5531_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5473_, v___x_5530_);
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 0, v___x_5531_);
v___x_5533_ = v___x_5528_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v___x_5531_);
lean_ctor_set_uint64(v_reuseFailAlloc_5542_, sizeof(void*)*1, v_tid_5526_);
v___x_5533_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
lean_object* v___x_5535_; 
if (v_isShared_5525_ == 0)
{
lean_ctor_set(v___x_5524_, 4, v___x_5533_);
v___x_5535_ = v___x_5524_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_env_5515_);
lean_ctor_set(v_reuseFailAlloc_5541_, 1, v_nextMacroScope_5516_);
lean_ctor_set(v_reuseFailAlloc_5541_, 2, v_ngen_5517_);
lean_ctor_set(v_reuseFailAlloc_5541_, 3, v_auxDeclNGen_5518_);
lean_ctor_set(v_reuseFailAlloc_5541_, 4, v___x_5533_);
lean_ctor_set(v_reuseFailAlloc_5541_, 5, v_cache_5519_);
lean_ctor_set(v_reuseFailAlloc_5541_, 6, v_messages_5520_);
lean_ctor_set(v_reuseFailAlloc_5541_, 7, v_infoState_5521_);
lean_ctor_set(v_reuseFailAlloc_5541_, 8, v_snapshotTasks_5522_);
v___x_5535_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5539_; 
v___x_5536_ = lean_st_ref_set(v___y_5480_, v___x_5535_);
v___x_5537_ = lean_box(0);
if (v_isShared_5512_ == 0)
{
lean_ctor_set(v___x_5511_, 0, v___x_5537_);
v___x_5539_ = v___x_5511_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v___x_5537_);
v___x_5539_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
return v___x_5539_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_5547_, lean_object* v_data_5548_, lean_object* v_ref_5549_, lean_object* v_msg_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_){
_start:
{
lean_object* v_res_5556_; 
v_res_5556_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_5547_, v_data_5548_, v_ref_5549_, v_msg_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_);
lean_dec(v___y_5554_);
lean_dec_ref(v___y_5553_);
lean_dec(v___y_5552_);
lean_dec_ref(v___y_5551_);
return v_res_5556_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5558_; lean_object* v___x_5559_; 
v___x_5558_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0));
v___x_5559_ = l_Lean_stringToMessageData(v___x_5558_);
return v___x_5559_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2(void){
_start:
{
lean_object* v___x_5560_; double v___x_5561_; 
v___x_5560_ = lean_unsigned_to_nat(1000u);
v___x_5561_ = lean_float_of_nat(v___x_5560_);
return v___x_5561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object* v_cls_5562_, uint8_t v_collapsed_5563_, lean_object* v_tag_5564_, lean_object* v_opts_5565_, uint8_t v_clsEnabled_5566_, lean_object* v_oldTraces_5567_, lean_object* v_msg_5568_, lean_object* v_resStartStop_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_){
_start:
{
lean_object* v_fst_5582_; lean_object* v_snd_5583_; lean_object* v___y_5585_; lean_object* v___y_5586_; lean_object* v_data_5587_; lean_object* v_fst_5598_; lean_object* v_snd_5599_; lean_object* v___x_5600_; uint8_t v___x_5601_; lean_object* v___y_5603_; lean_object* v_a_5604_; uint8_t v___y_5619_; double v___y_5650_; 
v_fst_5582_ = lean_ctor_get(v_resStartStop_5569_, 0);
lean_inc(v_fst_5582_);
v_snd_5583_ = lean_ctor_get(v_resStartStop_5569_, 1);
lean_inc(v_snd_5583_);
lean_dec_ref(v_resStartStop_5569_);
v_fst_5598_ = lean_ctor_get(v_snd_5583_, 0);
lean_inc(v_fst_5598_);
v_snd_5599_ = lean_ctor_get(v_snd_5583_, 1);
lean_inc(v_snd_5599_);
lean_dec(v_snd_5583_);
v___x_5600_ = l_Lean_trace_profiler;
v___x_5601_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_5565_, v___x_5600_);
if (v___x_5601_ == 0)
{
v___y_5619_ = v___x_5601_;
goto v___jp_5618_;
}
else
{
lean_object* v___x_5655_; uint8_t v___x_5656_; 
v___x_5655_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5656_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_5565_, v___x_5655_);
if (v___x_5656_ == 0)
{
lean_object* v___x_5657_; lean_object* v___x_5658_; double v___x_5659_; double v___x_5660_; double v___x_5661_; 
v___x_5657_ = l_Lean_trace_profiler_threshold;
v___x_5658_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_5565_, v___x_5657_);
v___x_5659_ = lean_float_of_nat(v___x_5658_);
v___x_5660_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_5661_ = lean_float_div(v___x_5659_, v___x_5660_);
v___y_5650_ = v___x_5661_;
goto v___jp_5649_;
}
else
{
lean_object* v___x_5662_; lean_object* v___x_5663_; double v___x_5664_; 
v___x_5662_ = l_Lean_trace_profiler_threshold;
v___x_5663_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_5565_, v___x_5662_);
v___x_5664_ = lean_float_of_nat(v___x_5663_);
v___y_5650_ = v___x_5664_;
goto v___jp_5649_;
}
}
v___jp_5584_:
{
lean_object* v___x_5588_; 
lean_inc(v___y_5586_);
v___x_5588_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_5567_, v_data_5587_, v___y_5586_, v___y_5585_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_);
if (lean_obj_tag(v___x_5588_) == 0)
{
lean_object* v___x_5589_; 
lean_dec_ref_known(v___x_5588_, 1);
v___x_5589_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_5582_);
return v___x_5589_;
}
else
{
lean_object* v_a_5590_; lean_object* v___x_5592_; uint8_t v_isShared_5593_; uint8_t v_isSharedCheck_5597_; 
lean_dec(v_fst_5582_);
v_a_5590_ = lean_ctor_get(v___x_5588_, 0);
v_isSharedCheck_5597_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5597_ == 0)
{
v___x_5592_ = v___x_5588_;
v_isShared_5593_ = v_isSharedCheck_5597_;
goto v_resetjp_5591_;
}
else
{
lean_inc(v_a_5590_);
lean_dec(v___x_5588_);
v___x_5592_ = lean_box(0);
v_isShared_5593_ = v_isSharedCheck_5597_;
goto v_resetjp_5591_;
}
v_resetjp_5591_:
{
lean_object* v___x_5595_; 
if (v_isShared_5593_ == 0)
{
v___x_5595_ = v___x_5592_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_a_5590_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
return v___x_5595_;
}
}
}
}
v___jp_5602_:
{
uint8_t v_result_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; double v___x_5608_; lean_object* v_data_5609_; 
v_result_5605_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_fst_5582_);
v___x_5606_ = lean_box(v_result_5605_);
v___x_5607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5607_, 0, v___x_5606_);
v___x_5608_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_5564_);
lean_inc_ref(v___x_5607_);
lean_inc(v_cls_5562_);
v_data_5609_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5609_, 0, v_cls_5562_);
lean_ctor_set(v_data_5609_, 1, v___x_5607_);
lean_ctor_set(v_data_5609_, 2, v_tag_5564_);
lean_ctor_set_float(v_data_5609_, sizeof(void*)*3, v___x_5608_);
lean_ctor_set_float(v_data_5609_, sizeof(void*)*3 + 8, v___x_5608_);
lean_ctor_set_uint8(v_data_5609_, sizeof(void*)*3 + 16, v_collapsed_5563_);
if (v___x_5601_ == 0)
{
lean_dec_ref_known(v___x_5607_, 1);
lean_dec(v_snd_5599_);
lean_dec(v_fst_5598_);
lean_dec_ref(v_tag_5564_);
lean_dec(v_cls_5562_);
v___y_5585_ = v_a_5604_;
v___y_5586_ = v___y_5603_;
v_data_5587_ = v_data_5609_;
goto v___jp_5584_;
}
else
{
lean_object* v_data_5610_; double v___x_5611_; double v___x_5612_; 
lean_dec_ref_known(v_data_5609_, 3);
v_data_5610_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5610_, 0, v_cls_5562_);
lean_ctor_set(v_data_5610_, 1, v___x_5607_);
lean_ctor_set(v_data_5610_, 2, v_tag_5564_);
v___x_5611_ = lean_unbox_float(v_fst_5598_);
lean_dec(v_fst_5598_);
lean_ctor_set_float(v_data_5610_, sizeof(void*)*3, v___x_5611_);
v___x_5612_ = lean_unbox_float(v_snd_5599_);
lean_dec(v_snd_5599_);
lean_ctor_set_float(v_data_5610_, sizeof(void*)*3 + 8, v___x_5612_);
lean_ctor_set_uint8(v_data_5610_, sizeof(void*)*3 + 16, v_collapsed_5563_);
v___y_5585_ = v_a_5604_;
v___y_5586_ = v___y_5603_;
v_data_5587_ = v_data_5610_;
goto v___jp_5584_;
}
}
v___jp_5613_:
{
lean_object* v_ref_5614_; lean_object* v___x_5615_; 
v_ref_5614_ = lean_ctor_get(v___y_5579_, 5);
lean_inc(v___y_5580_);
lean_inc_ref(v___y_5579_);
lean_inc(v___y_5578_);
lean_inc_ref(v___y_5577_);
lean_inc(v___y_5576_);
lean_inc_ref(v___y_5575_);
lean_inc(v___y_5574_);
lean_inc_ref(v___y_5573_);
lean_inc(v___y_5572_);
lean_inc(v___y_5571_);
lean_inc_ref(v___y_5570_);
lean_inc(v_fst_5582_);
v___x_5615_ = lean_apply_13(v_msg_5568_, v_fst_5582_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, lean_box(0));
if (lean_obj_tag(v___x_5615_) == 0)
{
lean_object* v_a_5616_; 
v_a_5616_ = lean_ctor_get(v___x_5615_, 0);
lean_inc(v_a_5616_);
lean_dec_ref_known(v___x_5615_, 1);
v___y_5603_ = v_ref_5614_;
v_a_5604_ = v_a_5616_;
goto v___jp_5602_;
}
else
{
lean_object* v___x_5617_; 
lean_dec_ref_known(v___x_5615_, 1);
v___x_5617_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1);
v___y_5603_ = v_ref_5614_;
v_a_5604_ = v___x_5617_;
goto v___jp_5602_;
}
}
v___jp_5618_:
{
if (v_clsEnabled_5566_ == 0)
{
if (v___y_5619_ == 0)
{
lean_object* v___x_5620_; lean_object* v_traceState_5621_; lean_object* v_env_5622_; lean_object* v_nextMacroScope_5623_; lean_object* v_ngen_5624_; lean_object* v_auxDeclNGen_5625_; lean_object* v_cache_5626_; lean_object* v_messages_5627_; lean_object* v_infoState_5628_; lean_object* v_snapshotTasks_5629_; lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5648_; 
lean_dec(v_snd_5599_);
lean_dec(v_fst_5598_);
lean_dec_ref(v_msg_5568_);
lean_dec_ref(v_tag_5564_);
lean_dec(v_cls_5562_);
v___x_5620_ = lean_st_ref_take(v___y_5580_);
v_traceState_5621_ = lean_ctor_get(v___x_5620_, 4);
v_env_5622_ = lean_ctor_get(v___x_5620_, 0);
v_nextMacroScope_5623_ = lean_ctor_get(v___x_5620_, 1);
v_ngen_5624_ = lean_ctor_get(v___x_5620_, 2);
v_auxDeclNGen_5625_ = lean_ctor_get(v___x_5620_, 3);
v_cache_5626_ = lean_ctor_get(v___x_5620_, 5);
v_messages_5627_ = lean_ctor_get(v___x_5620_, 6);
v_infoState_5628_ = lean_ctor_get(v___x_5620_, 7);
v_snapshotTasks_5629_ = lean_ctor_get(v___x_5620_, 8);
v_isSharedCheck_5648_ = !lean_is_exclusive(v___x_5620_);
if (v_isSharedCheck_5648_ == 0)
{
v___x_5631_ = v___x_5620_;
v_isShared_5632_ = v_isSharedCheck_5648_;
goto v_resetjp_5630_;
}
else
{
lean_inc(v_snapshotTasks_5629_);
lean_inc(v_infoState_5628_);
lean_inc(v_messages_5627_);
lean_inc(v_cache_5626_);
lean_inc(v_traceState_5621_);
lean_inc(v_auxDeclNGen_5625_);
lean_inc(v_ngen_5624_);
lean_inc(v_nextMacroScope_5623_);
lean_inc(v_env_5622_);
lean_dec(v___x_5620_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5648_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
uint64_t v_tid_5633_; lean_object* v_traces_5634_; lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5647_; 
v_tid_5633_ = lean_ctor_get_uint64(v_traceState_5621_, sizeof(void*)*1);
v_traces_5634_ = lean_ctor_get(v_traceState_5621_, 0);
v_isSharedCheck_5647_ = !lean_is_exclusive(v_traceState_5621_);
if (v_isSharedCheck_5647_ == 0)
{
v___x_5636_ = v_traceState_5621_;
v_isShared_5637_ = v_isSharedCheck_5647_;
goto v_resetjp_5635_;
}
else
{
lean_inc(v_traces_5634_);
lean_dec(v_traceState_5621_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5647_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v___x_5638_; lean_object* v___x_5640_; 
v___x_5638_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5567_, v_traces_5634_);
lean_dec_ref(v_traces_5634_);
if (v_isShared_5637_ == 0)
{
lean_ctor_set(v___x_5636_, 0, v___x_5638_);
v___x_5640_ = v___x_5636_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v___x_5638_);
lean_ctor_set_uint64(v_reuseFailAlloc_5646_, sizeof(void*)*1, v_tid_5633_);
v___x_5640_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
lean_object* v___x_5642_; 
if (v_isShared_5632_ == 0)
{
lean_ctor_set(v___x_5631_, 4, v___x_5640_);
v___x_5642_ = v___x_5631_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5645_; 
v_reuseFailAlloc_5645_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_env_5622_);
lean_ctor_set(v_reuseFailAlloc_5645_, 1, v_nextMacroScope_5623_);
lean_ctor_set(v_reuseFailAlloc_5645_, 2, v_ngen_5624_);
lean_ctor_set(v_reuseFailAlloc_5645_, 3, v_auxDeclNGen_5625_);
lean_ctor_set(v_reuseFailAlloc_5645_, 4, v___x_5640_);
lean_ctor_set(v_reuseFailAlloc_5645_, 5, v_cache_5626_);
lean_ctor_set(v_reuseFailAlloc_5645_, 6, v_messages_5627_);
lean_ctor_set(v_reuseFailAlloc_5645_, 7, v_infoState_5628_);
lean_ctor_set(v_reuseFailAlloc_5645_, 8, v_snapshotTasks_5629_);
v___x_5642_ = v_reuseFailAlloc_5645_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
lean_object* v___x_5643_; lean_object* v___x_5644_; 
v___x_5643_ = lean_st_ref_set(v___y_5580_, v___x_5642_);
v___x_5644_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_5582_);
return v___x_5644_;
}
}
}
}
}
else
{
goto v___jp_5613_;
}
}
else
{
goto v___jp_5613_;
}
}
v___jp_5649_:
{
double v___x_5651_; double v___x_5652_; double v___x_5653_; uint8_t v___x_5654_; 
v___x_5651_ = lean_unbox_float(v_snd_5599_);
v___x_5652_ = lean_unbox_float(v_fst_5598_);
v___x_5653_ = lean_float_sub(v___x_5651_, v___x_5652_);
v___x_5654_ = lean_float_decLt(v___y_5650_, v___x_5653_);
v___y_5619_ = v___x_5654_;
goto v___jp_5618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_5665_ = _args[0];
lean_object* v_collapsed_5666_ = _args[1];
lean_object* v_tag_5667_ = _args[2];
lean_object* v_opts_5668_ = _args[3];
lean_object* v_clsEnabled_5669_ = _args[4];
lean_object* v_oldTraces_5670_ = _args[5];
lean_object* v_msg_5671_ = _args[6];
lean_object* v_resStartStop_5672_ = _args[7];
lean_object* v___y_5673_ = _args[8];
lean_object* v___y_5674_ = _args[9];
lean_object* v___y_5675_ = _args[10];
lean_object* v___y_5676_ = _args[11];
lean_object* v___y_5677_ = _args[12];
lean_object* v___y_5678_ = _args[13];
lean_object* v___y_5679_ = _args[14];
lean_object* v___y_5680_ = _args[15];
lean_object* v___y_5681_ = _args[16];
lean_object* v___y_5682_ = _args[17];
lean_object* v___y_5683_ = _args[18];
lean_object* v___y_5684_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_5685_; uint8_t v_clsEnabled_boxed_5686_; lean_object* v_res_5687_; 
v_collapsed_boxed_5685_ = lean_unbox(v_collapsed_5666_);
v_clsEnabled_boxed_5686_ = lean_unbox(v_clsEnabled_5669_);
v_res_5687_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_5665_, v_collapsed_boxed_5685_, v_tag_5667_, v_opts_5668_, v_clsEnabled_boxed_5686_, v_oldTraces_5670_, v_msg_5671_, v_resStartStop_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5678_);
lean_dec(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec(v___y_5675_);
lean_dec(v___y_5674_);
lean_dec_ref(v___y_5673_);
lean_dec_ref(v_opts_5668_);
return v_res_5687_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_5692_; lean_object* v___x_5693_; 
v___x_5692_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_5693_ = l_Lean_stringToMessageData(v___x_5692_);
return v___x_5693_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_5694_, lean_object* v_b_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_){
_start:
{
if (lean_obj_tag(v_as_x27_5694_) == 0)
{
lean_object* v___x_5708_; 
v___x_5708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5708_, 0, v_b_5695_);
return v___x_5708_;
}
else
{
lean_object* v_head_5709_; lean_object* v_options_5710_; lean_object* v_tail_5711_; lean_object* v_name_5712_; lean_object* v_run_x27_5713_; lean_object* v_inheritedTraceOptions_5714_; uint8_t v_hasTrace_5715_; lean_object* v___x_5716_; uint8_t v___y_5718_; lean_object* v___x_5723_; lean_object* v___y_5725_; 
lean_dec_ref(v_b_5695_);
v_head_5709_ = lean_ctor_get(v_as_x27_5694_, 0);
v_options_5710_ = lean_ctor_get(v___y_5705_, 2);
v_tail_5711_ = lean_ctor_get(v_as_x27_5694_, 1);
v_name_5712_ = lean_ctor_get(v_head_5709_, 0);
v_run_x27_5713_ = lean_ctor_get(v_head_5709_, 1);
v_inheritedTraceOptions_5714_ = lean_ctor_get(v___y_5705_, 13);
v_hasTrace_5715_ = lean_ctor_get_uint8(v_options_5710_, sizeof(void*)*1);
v___x_5716_ = lean_box(0);
v___x_5723_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_5715_ == 0)
{
lean_object* v___x_5753_; 
lean_inc_ref(v_run_x27_5713_);
lean_inc(v___y_5706_);
lean_inc_ref(v___y_5705_);
lean_inc(v___y_5704_);
lean_inc_ref(v___y_5703_);
lean_inc(v___y_5702_);
lean_inc_ref(v___y_5701_);
lean_inc(v___y_5700_);
lean_inc_ref(v___y_5699_);
lean_inc(v___y_5698_);
lean_inc(v___y_5697_);
lean_inc_ref(v___y_5696_);
v___x_5753_ = lean_apply_12(v_run_x27_5713_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_, lean_box(0));
v___y_5725_ = v___x_5753_;
goto v___jp_5724_;
}
else
{
lean_object* v___f_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; uint8_t v___x_5758_; lean_object* v___y_5760_; lean_object* v___y_5761_; lean_object* v_a_5762_; lean_object* v___y_5775_; lean_object* v___y_5776_; lean_object* v_a_5777_; 
lean_inc(v_name_5712_);
v___f_5754_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 14, 1);
lean_closure_set(v___f_5754_, 0, v_name_5712_);
v___x_5755_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
v___x_5756_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5757_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___x_5758_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5714_, v_options_5710_, v___x_5757_);
if (v___x_5758_ == 0)
{
lean_object* v___x_5827_; uint8_t v___x_5828_; 
v___x_5827_ = l_Lean_trace_profiler;
v___x_5828_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_5710_, v___x_5827_);
if (v___x_5828_ == 0)
{
lean_object* v___x_5829_; 
lean_dec_ref(v___f_5754_);
lean_inc_ref(v_run_x27_5713_);
lean_inc(v___y_5706_);
lean_inc_ref(v___y_5705_);
lean_inc(v___y_5704_);
lean_inc_ref(v___y_5703_);
lean_inc(v___y_5702_);
lean_inc_ref(v___y_5701_);
lean_inc(v___y_5700_);
lean_inc_ref(v___y_5699_);
lean_inc(v___y_5698_);
lean_inc(v___y_5697_);
lean_inc_ref(v___y_5696_);
v___x_5829_ = lean_apply_12(v_run_x27_5713_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_, lean_box(0));
v___y_5725_ = v___x_5829_;
goto v___jp_5724_;
}
else
{
goto v___jp_5786_;
}
}
else
{
goto v___jp_5786_;
}
v___jp_5759_:
{
lean_object* v___x_5763_; double v___x_5764_; double v___x_5765_; double v___x_5766_; double v___x_5767_; double v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; 
v___x_5763_ = lean_io_mono_nanos_now();
v___x_5764_ = lean_float_of_nat(v___y_5761_);
v___x_5765_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13);
v___x_5766_ = lean_float_div(v___x_5764_, v___x_5765_);
v___x_5767_ = lean_float_of_nat(v___x_5763_);
v___x_5768_ = lean_float_div(v___x_5767_, v___x_5765_);
v___x_5769_ = lean_box_float(v___x_5766_);
v___x_5770_ = lean_box_float(v___x_5768_);
v___x_5771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5771_, 0, v___x_5769_);
lean_ctor_set(v___x_5771_, 1, v___x_5770_);
v___x_5772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5772_, 0, v_a_5762_);
lean_ctor_set(v___x_5772_, 1, v___x_5771_);
v___x_5773_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_5755_, v_hasTrace_5715_, v___x_5756_, v_options_5710_, v___x_5758_, v___y_5760_, v___f_5754_, v___x_5772_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_);
v___y_5725_ = v___x_5773_;
goto v___jp_5724_;
}
v___jp_5774_:
{
lean_object* v___x_5778_; double v___x_5779_; double v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; 
v___x_5778_ = lean_io_get_num_heartbeats();
v___x_5779_ = lean_float_of_nat(v___y_5776_);
v___x_5780_ = lean_float_of_nat(v___x_5778_);
v___x_5781_ = lean_box_float(v___x_5779_);
v___x_5782_ = lean_box_float(v___x_5780_);
v___x_5783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5783_, 0, v___x_5781_);
lean_ctor_set(v___x_5783_, 1, v___x_5782_);
v___x_5784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5784_, 0, v_a_5777_);
lean_ctor_set(v___x_5784_, 1, v___x_5783_);
v___x_5785_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_5755_, v_hasTrace_5715_, v___x_5756_, v_options_5710_, v___x_5758_, v___y_5775_, v___f_5754_, v___x_5784_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_);
v___y_5725_ = v___x_5785_;
goto v___jp_5724_;
}
v___jp_5786_:
{
lean_object* v___x_5787_; lean_object* v_a_5788_; lean_object* v___x_5789_; uint8_t v___x_5790_; 
v___x_5787_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_5706_);
v_a_5788_ = lean_ctor_get(v___x_5787_, 0);
lean_inc(v_a_5788_);
lean_dec_ref(v___x_5787_);
v___x_5789_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5790_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_5710_, v___x_5789_);
if (v___x_5790_ == 0)
{
lean_object* v___x_5791_; lean_object* v___x_5792_; 
v___x_5791_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_5713_);
lean_inc(v___y_5706_);
lean_inc_ref(v___y_5705_);
lean_inc(v___y_5704_);
lean_inc_ref(v___y_5703_);
lean_inc(v___y_5702_);
lean_inc_ref(v___y_5701_);
lean_inc(v___y_5700_);
lean_inc_ref(v___y_5699_);
lean_inc(v___y_5698_);
lean_inc(v___y_5697_);
lean_inc_ref(v___y_5696_);
v___x_5792_ = lean_apply_12(v_run_x27_5713_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_, lean_box(0));
if (lean_obj_tag(v___x_5792_) == 0)
{
lean_object* v_a_5793_; lean_object* v___x_5795_; uint8_t v_isShared_5796_; uint8_t v_isSharedCheck_5800_; 
v_a_5793_ = lean_ctor_get(v___x_5792_, 0);
v_isSharedCheck_5800_ = !lean_is_exclusive(v___x_5792_);
if (v_isSharedCheck_5800_ == 0)
{
v___x_5795_ = v___x_5792_;
v_isShared_5796_ = v_isSharedCheck_5800_;
goto v_resetjp_5794_;
}
else
{
lean_inc(v_a_5793_);
lean_dec(v___x_5792_);
v___x_5795_ = lean_box(0);
v_isShared_5796_ = v_isSharedCheck_5800_;
goto v_resetjp_5794_;
}
v_resetjp_5794_:
{
lean_object* v___x_5798_; 
if (v_isShared_5796_ == 0)
{
lean_ctor_set_tag(v___x_5795_, 1);
v___x_5798_ = v___x_5795_;
goto v_reusejp_5797_;
}
else
{
lean_object* v_reuseFailAlloc_5799_; 
v_reuseFailAlloc_5799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5799_, 0, v_a_5793_);
v___x_5798_ = v_reuseFailAlloc_5799_;
goto v_reusejp_5797_;
}
v_reusejp_5797_:
{
v___y_5760_ = v_a_5788_;
v___y_5761_ = v___x_5791_;
v_a_5762_ = v___x_5798_;
goto v___jp_5759_;
}
}
}
else
{
lean_object* v_a_5801_; lean_object* v___x_5803_; uint8_t v_isShared_5804_; uint8_t v_isSharedCheck_5808_; 
v_a_5801_ = lean_ctor_get(v___x_5792_, 0);
v_isSharedCheck_5808_ = !lean_is_exclusive(v___x_5792_);
if (v_isSharedCheck_5808_ == 0)
{
v___x_5803_ = v___x_5792_;
v_isShared_5804_ = v_isSharedCheck_5808_;
goto v_resetjp_5802_;
}
else
{
lean_inc(v_a_5801_);
lean_dec(v___x_5792_);
v___x_5803_ = lean_box(0);
v_isShared_5804_ = v_isSharedCheck_5808_;
goto v_resetjp_5802_;
}
v_resetjp_5802_:
{
lean_object* v___x_5806_; 
if (v_isShared_5804_ == 0)
{
lean_ctor_set_tag(v___x_5803_, 0);
v___x_5806_ = v___x_5803_;
goto v_reusejp_5805_;
}
else
{
lean_object* v_reuseFailAlloc_5807_; 
v_reuseFailAlloc_5807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5807_, 0, v_a_5801_);
v___x_5806_ = v_reuseFailAlloc_5807_;
goto v_reusejp_5805_;
}
v_reusejp_5805_:
{
v___y_5760_ = v_a_5788_;
v___y_5761_ = v___x_5791_;
v_a_5762_ = v___x_5806_;
goto v___jp_5759_;
}
}
}
}
else
{
lean_object* v___x_5809_; lean_object* v___x_5810_; 
v___x_5809_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_5713_);
lean_inc(v___y_5706_);
lean_inc_ref(v___y_5705_);
lean_inc(v___y_5704_);
lean_inc_ref(v___y_5703_);
lean_inc(v___y_5702_);
lean_inc_ref(v___y_5701_);
lean_inc(v___y_5700_);
lean_inc_ref(v___y_5699_);
lean_inc(v___y_5698_);
lean_inc(v___y_5697_);
lean_inc_ref(v___y_5696_);
v___x_5810_ = lean_apply_12(v_run_x27_5713_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_, lean_box(0));
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v_a_5811_; lean_object* v___x_5813_; uint8_t v_isShared_5814_; uint8_t v_isSharedCheck_5818_; 
v_a_5811_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5818_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5818_ == 0)
{
v___x_5813_ = v___x_5810_;
v_isShared_5814_ = v_isSharedCheck_5818_;
goto v_resetjp_5812_;
}
else
{
lean_inc(v_a_5811_);
lean_dec(v___x_5810_);
v___x_5813_ = lean_box(0);
v_isShared_5814_ = v_isSharedCheck_5818_;
goto v_resetjp_5812_;
}
v_resetjp_5812_:
{
lean_object* v___x_5816_; 
if (v_isShared_5814_ == 0)
{
lean_ctor_set_tag(v___x_5813_, 1);
v___x_5816_ = v___x_5813_;
goto v_reusejp_5815_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v_a_5811_);
v___x_5816_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5815_;
}
v_reusejp_5815_:
{
v___y_5775_ = v_a_5788_;
v___y_5776_ = v___x_5809_;
v_a_5777_ = v___x_5816_;
goto v___jp_5774_;
}
}
}
else
{
lean_object* v_a_5819_; lean_object* v___x_5821_; uint8_t v_isShared_5822_; uint8_t v_isSharedCheck_5826_; 
v_a_5819_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5826_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5826_ == 0)
{
v___x_5821_ = v___x_5810_;
v_isShared_5822_ = v_isSharedCheck_5826_;
goto v_resetjp_5820_;
}
else
{
lean_inc(v_a_5819_);
lean_dec(v___x_5810_);
v___x_5821_ = lean_box(0);
v_isShared_5822_ = v_isSharedCheck_5826_;
goto v_resetjp_5820_;
}
v_resetjp_5820_:
{
lean_object* v___x_5824_; 
if (v_isShared_5822_ == 0)
{
lean_ctor_set_tag(v___x_5821_, 0);
v___x_5824_ = v___x_5821_;
goto v_reusejp_5823_;
}
else
{
lean_object* v_reuseFailAlloc_5825_; 
v_reuseFailAlloc_5825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5825_, 0, v_a_5819_);
v___x_5824_ = v_reuseFailAlloc_5825_;
goto v_reusejp_5823_;
}
v_reusejp_5823_:
{
v___y_5775_ = v_a_5788_;
v___y_5776_ = v___x_5809_;
v_a_5777_ = v___x_5824_;
goto v___jp_5774_;
}
}
}
}
}
}
v___jp_5717_:
{
lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; 
v___x_5719_ = lean_box(v___y_5718_);
v___x_5720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5719_);
v___x_5721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5720_);
lean_ctor_set(v___x_5721_, 1, v___x_5716_);
v___x_5722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5721_);
return v___x_5722_;
}
v___jp_5724_:
{
if (lean_obj_tag(v___y_5725_) == 0)
{
lean_object* v_a_5726_; uint8_t v___x_5727_; 
v_a_5726_ = lean_ctor_get(v___y_5725_, 0);
lean_inc(v_a_5726_);
lean_dec_ref_known(v___y_5725_, 1);
v___x_5727_ = lean_unbox(v_a_5726_);
if (v___x_5727_ == 0)
{
lean_dec(v_a_5726_);
v_as_x27_5694_ = v_tail_5711_;
v_b_5695_ = v___x_5723_;
goto _start;
}
else
{
if (v_hasTrace_5715_ == 0)
{
uint8_t v___x_5729_; 
v___x_5729_ = lean_unbox(v_a_5726_);
lean_dec(v_a_5726_);
v___y_5718_ = v___x_5729_;
goto v___jp_5717_;
}
else
{
lean_object* v___x_5730_; lean_object* v___x_5731_; uint8_t v___x_5732_; 
v___x_5730_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
v___x_5731_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___x_5732_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5714_, v_options_5710_, v___x_5731_);
if (v___x_5732_ == 0)
{
uint8_t v___x_5733_; 
v___x_5733_ = lean_unbox(v_a_5726_);
lean_dec(v_a_5726_);
v___y_5718_ = v___x_5733_;
goto v___jp_5717_;
}
else
{
lean_object* v___x_5734_; lean_object* v___x_5735_; 
v___x_5734_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2);
v___x_5735_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_5730_, v___x_5734_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_);
if (lean_obj_tag(v___x_5735_) == 0)
{
uint8_t v___x_5736_; 
lean_dec_ref_known(v___x_5735_, 1);
v___x_5736_ = lean_unbox(v_a_5726_);
lean_dec(v_a_5726_);
v___y_5718_ = v___x_5736_;
goto v___jp_5717_;
}
else
{
lean_object* v_a_5737_; lean_object* v___x_5739_; uint8_t v_isShared_5740_; uint8_t v_isSharedCheck_5744_; 
lean_dec(v_a_5726_);
v_a_5737_ = lean_ctor_get(v___x_5735_, 0);
v_isSharedCheck_5744_ = !lean_is_exclusive(v___x_5735_);
if (v_isSharedCheck_5744_ == 0)
{
v___x_5739_ = v___x_5735_;
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
else
{
lean_inc(v_a_5737_);
lean_dec(v___x_5735_);
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
}
}
}
else
{
lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5752_; 
v_a_5745_ = lean_ctor_get(v___y_5725_, 0);
v_isSharedCheck_5752_ = !lean_is_exclusive(v___y_5725_);
if (v_isSharedCheck_5752_ == 0)
{
v___x_5747_ = v___y_5725_;
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_dec(v___y_5725_);
v___x_5747_ = lean_box(0);
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
v_resetjp_5746_:
{
lean_object* v___x_5750_; 
if (v_isShared_5748_ == 0)
{
v___x_5750_ = v___x_5747_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_a_5745_);
v___x_5750_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
return v___x_5750_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object* v_as_x27_5830_, lean_object* v_b_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_){
_start:
{
lean_object* v_res_5844_; 
v_res_5844_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_5830_, v_b_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_);
lean_dec(v___y_5842_);
lean_dec_ref(v___y_5841_);
lean_dec(v___y_5840_);
lean_dec_ref(v___y_5839_);
lean_dec(v___y_5838_);
lean_dec_ref(v___y_5837_);
lean_dec(v___y_5836_);
lean_dec_ref(v___y_5835_);
lean_dec(v___y_5834_);
lean_dec(v___y_5833_);
lean_dec_ref(v___y_5832_);
lean_dec(v_as_x27_5830_);
return v_res_5844_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2(void){
_start:
{
lean_object* v___x_5847_; lean_object* v___x_5848_; 
v___x_5847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1));
v___x_5848_ = l_Lean_stringToMessageData(v___x_5847_);
return v___x_5848_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4(void){
_start:
{
lean_object* v___x_5850_; lean_object* v___x_5851_; 
v___x_5850_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3));
v___x_5851_ = l_Lean_stringToMessageData(v___x_5850_);
return v___x_5851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object* v_passes_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_, lean_object* v_a_5856_, lean_object* v_a_5857_, lean_object* v_a_5858_, lean_object* v_a_5859_, lean_object* v_a_5860_, lean_object* v_a_5861_, lean_object* v_a_5862_, lean_object* v_a_5863_){
_start:
{
lean_object* v___x_5865_; lean_object* v___x_5866_; 
v___x_5865_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0));
v___x_5866_ = l_Lean_Core_checkSystem(v___x_5865_, v_a_5862_, v_a_5863_);
if (lean_obj_tag(v___x_5866_) == 0)
{
lean_object* v___x_5867_; lean_object* v_rewriteSimpCache_5868_; lean_object* v_rewriteDSimpCache_5869_; lean_object* v_acCache_5870_; lean_object* v_typeAnalysis_5871_; lean_object* v_target_5872_; lean_object* v_hypotheses_5873_; lean_object* v___x_5875_; uint8_t v_isShared_5876_; uint8_t v_isSharedCheck_5956_; 
lean_dec_ref_known(v___x_5866_, 1);
v___x_5867_ = lean_st_ref_take(v_a_5854_);
v_rewriteSimpCache_5868_ = lean_ctor_get(v___x_5867_, 0);
v_rewriteDSimpCache_5869_ = lean_ctor_get(v___x_5867_, 1);
v_acCache_5870_ = lean_ctor_get(v___x_5867_, 2);
v_typeAnalysis_5871_ = lean_ctor_get(v___x_5867_, 3);
v_target_5872_ = lean_ctor_get(v___x_5867_, 4);
v_hypotheses_5873_ = lean_ctor_get(v___x_5867_, 5);
v_isSharedCheck_5956_ = !lean_is_exclusive(v___x_5867_);
if (v_isSharedCheck_5956_ == 0)
{
v___x_5875_ = v___x_5867_;
v_isShared_5876_ = v_isSharedCheck_5956_;
goto v_resetjp_5874_;
}
else
{
lean_inc(v_hypotheses_5873_);
lean_inc(v_target_5872_);
lean_inc(v_typeAnalysis_5871_);
lean_inc(v_acCache_5870_);
lean_inc(v_rewriteDSimpCache_5869_);
lean_inc(v_rewriteSimpCache_5868_);
lean_dec(v___x_5867_);
v___x_5875_ = lean_box(0);
v_isShared_5876_ = v_isSharedCheck_5956_;
goto v_resetjp_5874_;
}
v_resetjp_5874_:
{
uint8_t v___x_5877_; lean_object* v___x_5879_; 
v___x_5877_ = 0;
if (v_isShared_5876_ == 0)
{
v___x_5879_ = v___x_5875_;
goto v_reusejp_5878_;
}
else
{
lean_object* v_reuseFailAlloc_5955_; 
v_reuseFailAlloc_5955_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5955_, 0, v_rewriteSimpCache_5868_);
lean_ctor_set(v_reuseFailAlloc_5955_, 1, v_rewriteDSimpCache_5869_);
lean_ctor_set(v_reuseFailAlloc_5955_, 2, v_acCache_5870_);
lean_ctor_set(v_reuseFailAlloc_5955_, 3, v_typeAnalysis_5871_);
lean_ctor_set(v_reuseFailAlloc_5955_, 4, v_target_5872_);
lean_ctor_set(v_reuseFailAlloc_5955_, 5, v_hypotheses_5873_);
v___x_5879_ = v_reuseFailAlloc_5955_;
goto v_reusejp_5878_;
}
v_reusejp_5878_:
{
lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; 
lean_ctor_set_uint8(v___x_5879_, sizeof(void*)*6, v___x_5877_);
v___x_5880_ = lean_st_ref_set(v_a_5854_, v___x_5879_);
v___x_5881_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
v___x_5882_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_passes_5852_, v___x_5881_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_, v_a_5859_, v_a_5860_, v_a_5861_, v_a_5862_, v_a_5863_);
if (lean_obj_tag(v___x_5882_) == 0)
{
lean_object* v_a_5883_; lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5946_; 
v_a_5883_ = lean_ctor_get(v___x_5882_, 0);
v_isSharedCheck_5946_ = !lean_is_exclusive(v___x_5882_);
if (v_isSharedCheck_5946_ == 0)
{
v___x_5885_ = v___x_5882_;
v_isShared_5886_ = v_isSharedCheck_5946_;
goto v_resetjp_5884_;
}
else
{
lean_inc(v_a_5883_);
lean_dec(v___x_5882_);
v___x_5885_ = lean_box(0);
v_isShared_5886_ = v_isSharedCheck_5946_;
goto v_resetjp_5884_;
}
v_resetjp_5884_:
{
lean_object* v_fst_5887_; 
v_fst_5887_ = lean_ctor_get(v_a_5883_, 0);
lean_inc(v_fst_5887_);
lean_dec(v_a_5883_);
if (lean_obj_tag(v_fst_5887_) == 0)
{
lean_object* v___x_5888_; uint8_t v_didChange_5889_; 
v___x_5888_ = lean_st_ref_get(v_a_5854_);
v_didChange_5889_ = lean_ctor_get_uint8(v___x_5888_, sizeof(void*)*6);
lean_dec(v___x_5888_);
if (v_didChange_5889_ == 0)
{
lean_object* v_options_5890_; uint8_t v_hasTrace_5891_; 
v_options_5890_ = lean_ctor_get(v_a_5862_, 2);
v_hasTrace_5891_ = lean_ctor_get_uint8(v_options_5890_, sizeof(void*)*1);
if (v_hasTrace_5891_ == 0)
{
lean_object* v___x_5892_; lean_object* v___x_5894_; 
v___x_5892_ = lean_box(v_didChange_5889_);
if (v_isShared_5886_ == 0)
{
lean_ctor_set(v___x_5885_, 0, v___x_5892_);
v___x_5894_ = v___x_5885_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v___x_5892_);
v___x_5894_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
return v___x_5894_;
}
}
else
{
lean_object* v_inheritedTraceOptions_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; uint8_t v___x_5899_; 
v_inheritedTraceOptions_5896_ = lean_ctor_get(v_a_5862_, 13);
v___x_5897_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
v___x_5898_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___x_5899_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5896_, v_options_5890_, v___x_5898_);
if (v___x_5899_ == 0)
{
lean_object* v___x_5900_; lean_object* v___x_5902_; 
v___x_5900_ = lean_box(v_didChange_5889_);
if (v_isShared_5886_ == 0)
{
lean_ctor_set(v___x_5885_, 0, v___x_5900_);
v___x_5902_ = v___x_5885_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v___x_5900_);
v___x_5902_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
return v___x_5902_;
}
}
else
{
lean_object* v___x_5904_; lean_object* v___x_5905_; 
lean_del_object(v___x_5885_);
v___x_5904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_5905_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_5897_, v___x_5904_, v_a_5860_, v_a_5861_, v_a_5862_, v_a_5863_);
if (lean_obj_tag(v___x_5905_) == 0)
{
lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5913_; 
v_isSharedCheck_5913_ = !lean_is_exclusive(v___x_5905_);
if (v_isSharedCheck_5913_ == 0)
{
lean_object* v_unused_5914_; 
v_unused_5914_ = lean_ctor_get(v___x_5905_, 0);
lean_dec(v_unused_5914_);
v___x_5907_ = v___x_5905_;
v_isShared_5908_ = v_isSharedCheck_5913_;
goto v_resetjp_5906_;
}
else
{
lean_dec(v___x_5905_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5913_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5909_; lean_object* v___x_5911_; 
v___x_5909_ = lean_box(v_didChange_5889_);
if (v_isShared_5908_ == 0)
{
lean_ctor_set(v___x_5907_, 0, v___x_5909_);
v___x_5911_ = v___x_5907_;
goto v_reusejp_5910_;
}
else
{
lean_object* v_reuseFailAlloc_5912_; 
v_reuseFailAlloc_5912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5912_, 0, v___x_5909_);
v___x_5911_ = v_reuseFailAlloc_5912_;
goto v_reusejp_5910_;
}
v_reusejp_5910_:
{
return v___x_5911_;
}
}
}
else
{
lean_object* v_a_5915_; lean_object* v___x_5917_; uint8_t v_isShared_5918_; uint8_t v_isSharedCheck_5922_; 
v_a_5915_ = lean_ctor_get(v___x_5905_, 0);
v_isSharedCheck_5922_ = !lean_is_exclusive(v___x_5905_);
if (v_isSharedCheck_5922_ == 0)
{
v___x_5917_ = v___x_5905_;
v_isShared_5918_ = v_isSharedCheck_5922_;
goto v_resetjp_5916_;
}
else
{
lean_inc(v_a_5915_);
lean_dec(v___x_5905_);
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
}
}
else
{
lean_object* v_options_5923_; uint8_t v_hasTrace_5924_; 
lean_del_object(v___x_5885_);
v_options_5923_ = lean_ctor_get(v_a_5862_, 2);
v_hasTrace_5924_ = lean_ctor_get_uint8(v_options_5923_, sizeof(void*)*1);
if (v_hasTrace_5924_ == 0)
{
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; uint8_t v___x_5929_; 
v_inheritedTraceOptions_5926_ = lean_ctor_get(v_a_5862_, 13);
v___x_5927_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20));
v___x_5928_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___x_5929_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5926_, v_options_5923_, v___x_5928_);
if (v___x_5929_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_5931_; lean_object* v___x_5932_; 
v___x_5931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_5932_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_5927_, v___x_5931_, v_a_5860_, v_a_5861_, v_a_5862_, v_a_5863_);
if (lean_obj_tag(v___x_5932_) == 0)
{
lean_dec_ref_known(v___x_5932_, 1);
goto _start;
}
else
{
lean_object* v_a_5934_; lean_object* v___x_5936_; uint8_t v_isShared_5937_; uint8_t v_isSharedCheck_5941_; 
v_a_5934_ = lean_ctor_get(v___x_5932_, 0);
v_isSharedCheck_5941_ = !lean_is_exclusive(v___x_5932_);
if (v_isSharedCheck_5941_ == 0)
{
v___x_5936_ = v___x_5932_;
v_isShared_5937_ = v_isSharedCheck_5941_;
goto v_resetjp_5935_;
}
else
{
lean_inc(v_a_5934_);
lean_dec(v___x_5932_);
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
}
}
}
else
{
lean_object* v_val_5942_; lean_object* v___x_5944_; 
v_val_5942_ = lean_ctor_get(v_fst_5887_, 0);
lean_inc(v_val_5942_);
lean_dec_ref_known(v_fst_5887_, 1);
if (v_isShared_5886_ == 0)
{
lean_ctor_set(v___x_5885_, 0, v_val_5942_);
v___x_5944_ = v___x_5885_;
goto v_reusejp_5943_;
}
else
{
lean_object* v_reuseFailAlloc_5945_; 
v_reuseFailAlloc_5945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5945_, 0, v_val_5942_);
v___x_5944_ = v_reuseFailAlloc_5945_;
goto v_reusejp_5943_;
}
v_reusejp_5943_:
{
return v___x_5944_;
}
}
}
}
else
{
lean_object* v_a_5947_; lean_object* v___x_5949_; uint8_t v_isShared_5950_; uint8_t v_isSharedCheck_5954_; 
v_a_5947_ = lean_ctor_get(v___x_5882_, 0);
v_isSharedCheck_5954_ = !lean_is_exclusive(v___x_5882_);
if (v_isSharedCheck_5954_ == 0)
{
v___x_5949_ = v___x_5882_;
v_isShared_5950_ = v_isSharedCheck_5954_;
goto v_resetjp_5948_;
}
else
{
lean_inc(v_a_5947_);
lean_dec(v___x_5882_);
v___x_5949_ = lean_box(0);
v_isShared_5950_ = v_isSharedCheck_5954_;
goto v_resetjp_5948_;
}
v_resetjp_5948_:
{
lean_object* v___x_5952_; 
if (v_isShared_5950_ == 0)
{
v___x_5952_ = v___x_5949_;
goto v_reusejp_5951_;
}
else
{
lean_object* v_reuseFailAlloc_5953_; 
v_reuseFailAlloc_5953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5953_, 0, v_a_5947_);
v___x_5952_ = v_reuseFailAlloc_5953_;
goto v_reusejp_5951_;
}
v_reusejp_5951_:
{
return v___x_5952_;
}
}
}
}
}
}
else
{
lean_object* v_a_5957_; lean_object* v___x_5959_; uint8_t v_isShared_5960_; uint8_t v_isSharedCheck_5964_; 
v_a_5957_ = lean_ctor_get(v___x_5866_, 0);
v_isSharedCheck_5964_ = !lean_is_exclusive(v___x_5866_);
if (v_isSharedCheck_5964_ == 0)
{
v___x_5959_ = v___x_5866_;
v_isShared_5960_ = v_isSharedCheck_5964_;
goto v_resetjp_5958_;
}
else
{
lean_inc(v_a_5957_);
lean_dec(v___x_5866_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_, lean_object* v_a_5975_, lean_object* v_a_5976_, lean_object* v_a_5977_){
_start:
{
lean_object* v_res_5978_; 
v_res_5978_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_5965_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_, v_a_5974_, v_a_5975_, v_a_5976_);
lean_dec(v_a_5976_);
lean_dec_ref(v_a_5975_);
lean_dec(v_a_5974_);
lean_dec_ref(v_a_5973_);
lean_dec(v_a_5972_);
lean_dec_ref(v_a_5971_);
lean_dec(v_a_5970_);
lean_dec_ref(v_a_5969_);
lean_dec(v_a_5968_);
lean_dec(v_a_5967_);
lean_dec_ref(v_a_5966_);
lean_dec(v_passes_5965_);
return v_res_5978_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_5979_, lean_object* v_msg_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_){
_start:
{
lean_object* v___x_5993_; 
v___x_5993_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_5979_, v_msg_5980_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_);
return v___x_5993_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_5994_, lean_object* v_msg_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_, lean_object* v___y_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_){
_start:
{
lean_object* v_res_6008_; 
v_res_6008_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_5994_, v_msg_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_);
lean_dec(v___y_6006_);
lean_dec_ref(v___y_6005_);
lean_dec(v___y_6004_);
lean_dec_ref(v___y_6003_);
lean_dec(v___y_6002_);
lean_dec_ref(v___y_6001_);
lean_dec(v___y_6000_);
lean_dec_ref(v___y_5999_);
lean_dec(v___y_5998_);
lean_dec(v___y_5997_);
lean_dec_ref(v___y_5996_);
return v_res_6008_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_6009_, lean_object* v_x_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_){
_start:
{
lean_object* v___x_6023_; 
v___x_6023_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_6010_);
return v___x_6023_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_6024_, lean_object* v_x_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_){
_start:
{
lean_object* v_res_6038_; 
v_res_6038_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_6024_, v_x_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_);
lean_dec(v___y_6036_);
lean_dec_ref(v___y_6035_);
lean_dec(v___y_6034_);
lean_dec_ref(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec_ref(v___y_6031_);
lean_dec(v___y_6030_);
lean_dec_ref(v___y_6029_);
lean_dec(v___y_6028_);
lean_dec(v___y_6027_);
lean_dec_ref(v___y_6026_);
return v_res_6038_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_6039_, lean_object* v_as_x27_6040_, lean_object* v_b_6041_, lean_object* v_a_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_){
_start:
{
lean_object* v___x_6055_; 
v___x_6055_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_6040_, v_b_6041_, v___y_6043_, v___y_6044_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_);
return v___x_6055_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_6056_, lean_object* v_as_x27_6057_, lean_object* v_b_6058_, lean_object* v_a_6059_, lean_object* v___y_6060_, lean_object* v___y_6061_, lean_object* v___y_6062_, lean_object* v___y_6063_, lean_object* v___y_6064_, lean_object* v___y_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_){
_start:
{
lean_object* v_res_6072_; 
v_res_6072_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_6056_, v_as_x27_6057_, v_b_6058_, v_a_6059_, v___y_6060_, v___y_6061_, v___y_6062_, v___y_6063_, v___y_6064_, v___y_6065_, v___y_6066_, v___y_6067_, v___y_6068_, v___y_6069_, v___y_6070_);
lean_dec(v___y_6070_);
lean_dec_ref(v___y_6069_);
lean_dec(v___y_6068_);
lean_dec_ref(v___y_6067_);
lean_dec(v___y_6066_);
lean_dec_ref(v___y_6065_);
lean_dec(v___y_6064_);
lean_dec_ref(v___y_6063_);
lean_dec(v___y_6062_);
lean_dec(v___y_6061_);
lean_dec_ref(v___y_6060_);
lean_dec(v_as_x27_6057_);
lean_dec(v_as_6056_);
return v_res_6072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_6073_, lean_object* v_data_6074_, lean_object* v_ref_6075_, lean_object* v_msg_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_){
_start:
{
lean_object* v___x_6089_; 
v___x_6089_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_6073_, v_data_6074_, v_ref_6075_, v_msg_6076_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_);
return v___x_6089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_6090_, lean_object* v_data_6091_, lean_object* v_ref_6092_, lean_object* v_msg_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_){
_start:
{
lean_object* v_res_6106_; 
v_res_6106_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_6090_, v_data_6091_, v_ref_6092_, v_msg_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_);
lean_dec(v___y_6104_);
lean_dec_ref(v___y_6103_);
lean_dec(v___y_6102_);
lean_dec_ref(v___y_6101_);
lean_dec(v___y_6100_);
lean_dec_ref(v___y_6099_);
lean_dec(v___y_6098_);
lean_dec_ref(v___y_6097_);
lean_dec(v___y_6096_);
lean_dec(v___y_6095_);
lean_dec_ref(v___y_6094_);
return v_res_6106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_6107_, lean_object* v_a_6108_, lean_object* v_a_6109_, lean_object* v_a_6110_, lean_object* v_a_6111_, lean_object* v_a_6112_, lean_object* v_a_6113_, lean_object* v_a_6114_, lean_object* v_a_6115_, lean_object* v_a_6116_, lean_object* v_a_6117_, lean_object* v_a_6118_){
_start:
{
lean_object* v___x_6120_; 
v___x_6120_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_6107_, v_a_6108_, v_a_6109_, v_a_6110_, v_a_6111_, v_a_6112_, v_a_6113_, v_a_6114_, v_a_6115_, v_a_6116_, v_a_6117_, v_a_6118_);
if (lean_obj_tag(v___x_6120_) == 0)
{
lean_object* v_a_6121_; lean_object* v___x_6122_; lean_object* v___x_6124_; uint8_t v_isShared_6125_; uint8_t v_isSharedCheck_6129_; 
v_a_6121_ = lean_ctor_get(v___x_6120_, 0);
lean_inc(v_a_6121_);
lean_dec_ref_known(v___x_6120_, 1);
v___x_6122_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(v_a_6109_);
v_isSharedCheck_6129_ = !lean_is_exclusive(v___x_6122_);
if (v_isSharedCheck_6129_ == 0)
{
lean_object* v_unused_6130_; 
v_unused_6130_ = lean_ctor_get(v___x_6122_, 0);
lean_dec(v_unused_6130_);
v___x_6124_ = v___x_6122_;
v_isShared_6125_ = v_isSharedCheck_6129_;
goto v_resetjp_6123_;
}
else
{
lean_dec(v___x_6122_);
v___x_6124_ = lean_box(0);
v_isShared_6125_ = v_isSharedCheck_6129_;
goto v_resetjp_6123_;
}
v_resetjp_6123_:
{
lean_object* v___x_6127_; 
if (v_isShared_6125_ == 0)
{
lean_ctor_set(v___x_6124_, 0, v_a_6121_);
v___x_6127_ = v___x_6124_;
goto v_reusejp_6126_;
}
else
{
lean_object* v_reuseFailAlloc_6128_; 
v_reuseFailAlloc_6128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6128_, 0, v_a_6121_);
v___x_6127_ = v_reuseFailAlloc_6128_;
goto v_reusejp_6126_;
}
v_reusejp_6126_:
{
return v___x_6127_;
}
}
}
else
{
return v___x_6120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_6131_, lean_object* v_a_6132_, lean_object* v_a_6133_, lean_object* v_a_6134_, lean_object* v_a_6135_, lean_object* v_a_6136_, lean_object* v_a_6137_, lean_object* v_a_6138_, lean_object* v_a_6139_, lean_object* v_a_6140_, lean_object* v_a_6141_, lean_object* v_a_6142_, lean_object* v_a_6143_){
_start:
{
lean_object* v_res_6144_; 
v_res_6144_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_6131_, v_a_6132_, v_a_6133_, v_a_6134_, v_a_6135_, v_a_6136_, v_a_6137_, v_a_6138_, v_a_6139_, v_a_6140_, v_a_6141_, v_a_6142_);
lean_dec(v_a_6142_);
lean_dec_ref(v_a_6141_);
lean_dec(v_a_6140_);
lean_dec_ref(v_a_6139_);
lean_dec(v_a_6138_);
lean_dec_ref(v_a_6137_);
lean_dec(v_a_6136_);
lean_dec_ref(v_a_6135_);
lean_dec(v_a_6134_);
lean_dec(v_a_6133_);
lean_dec_ref(v_a_6132_);
lean_dec(v_passes_6131_);
return v_res_6144_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default = _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default);
l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp = _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Attr(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ExprPtr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
