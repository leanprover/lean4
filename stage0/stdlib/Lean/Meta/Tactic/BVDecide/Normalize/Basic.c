// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Basic
// Imports: public import Lean.Meta.Tactic.BVDecide.Attr public import Std.Tactic.BVDecide.Syntax public import Lean.Meta.Sym.ExprPtr public import Lean.Meta.Sym.SymM public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.DSimp.Result
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
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instExceptToTraceResultBool___lam__0___boxed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__14_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__15_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__16_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__18_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25;
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Learned hypothesis: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Running pass: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object**);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Fixpoint iteration solved the goal"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(lean_object* v_x_40_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(v_x_43_);
lean_dec_ref(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(lean_object* v_t_45_, lean_object* v_k_46_){
_start:
{
lean_object* v_info_47_; lean_object* v_ctors_48_; lean_object* v___x_49_; 
v_info_47_ = lean_ctor_get(v_t_45_, 0);
lean_inc_ref(v_info_47_);
v_ctors_48_ = lean_ctor_get(v_t_45_, 1);
lean_inc_ref(v_ctors_48_);
lean_dec_ref(v_t_45_);
v___x_49_ = lean_apply_2(v_k_46_, v_info_47_, v_ctors_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(lean_object* v_motive_50_, lean_object* v_ctorIdx_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_k_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_52_, v_k_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(lean_object* v_motive_56_, lean_object* v_ctorIdx_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_k_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(v_motive_56_, v_ctorIdx_57_, v_t_58_, v_h_59_, v_k_60_);
lean_dec(v_ctorIdx_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(lean_object* v_t_62_, lean_object* v_simpleEnum_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_62_, v_simpleEnum_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_simpleEnum_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_66_, v_simpleEnum_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(lean_object* v_t_70_, lean_object* v_enumWithDefault_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_70_, v_enumWithDefault_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(lean_object* v_motive_73_, lean_object* v_t_74_, lean_object* v_h_75_, lean_object* v_enumWithDefault_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_74_, v_enumWithDefault_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx(lean_object* v_x_78_){
_start:
{
switch(lean_obj_tag(v_x_78_))
{
case 0:
{
lean_object* v___x_79_; 
v___x_79_ = lean_unsigned_to_nat(0u);
return v___x_79_;
}
case 1:
{
lean_object* v___x_80_; 
v___x_80_ = lean_unsigned_to_nat(1u);
return v___x_80_;
}
case 2:
{
lean_object* v___x_81_; 
v___x_81_ = lean_unsigned_to_nat(2u);
return v___x_81_;
}
default: 
{
lean_object* v___x_82_; 
v___x_82_ = lean_unsigned_to_nat(3u);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx___boxed(lean_object* v_x_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorIdx(v_x_83_);
lean_dec_ref(v_x_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(lean_object* v_t_85_, lean_object* v_k_86_){
_start:
{
switch(lean_obj_tag(v_t_85_))
{
case 2:
{
lean_object* v_e_87_; lean_object* v___x_88_; 
v_e_87_ = lean_ctor_get(v_t_85_, 0);
lean_inc_ref(v_e_87_);
lean_dec_ref_known(v_t_85_, 1);
v___x_88_ = lean_apply_1(v_k_86_, v_e_87_);
return v___x_88_;
}
case 3:
{
lean_object* v_s_89_; lean_object* v___x_90_; 
v_s_89_ = lean_ctor_get(v_t_85_, 0);
lean_inc_ref(v_s_89_);
lean_dec_ref_known(v_t_85_, 1);
v___x_90_ = lean_apply_1(v_k_86_, v_s_89_);
return v___x_90_;
}
default: 
{
lean_object* v_fvar_91_; lean_object* v___x_92_; 
v_fvar_91_ = lean_ctor_get(v_t_85_, 0);
lean_inc(v_fvar_91_);
lean_dec_ref(v_t_85_);
v___x_92_ = lean_apply_1(v_k_86_, v_fvar_91_);
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(lean_object* v_motive_93_, lean_object* v_ctorIdx_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_k_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_95_, v_k_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___boxed(lean_object* v_motive_99_, lean_object* v_ctorIdx_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_k_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim(v_motive_99_, v_ctorIdx_100_, v_t_101_, v_h_102_, v_k_103_);
lean_dec(v_ctorIdx_100_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim___redArg(lean_object* v_t_105_, lean_object* v_lctx_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_105_, v_lctx_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_lctx_elim(lean_object* v_motive_108_, lean_object* v_t_109_, lean_object* v_h_110_, lean_object* v_lctx_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_109_, v_lctx_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim___redArg(lean_object* v_t_113_, lean_object* v_enumDomain_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_113_, v_enumDomain_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_enumDomain_elim(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_enumDomain_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_117_, v_enumDomain_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim___redArg(lean_object* v_t_121_, lean_object* v_structureProjection_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_121_, v_structureProjection_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_structureProjection_elim(lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_structureProjection_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_125_, v_structureProjection_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim___redArg(lean_object* v_t_129_, lean_object* v_andFlattened_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_129_, v_andFlattened_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_andFlattened_elim(lean_object* v_motive_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_andFlattened_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_Tactic_BVDecide_Normalize_HypSource_ctorElim___redArg(v_t_133_, v_andFlattened_135_);
return v___x_136_;
}
}
static uint64_t _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0(void){
_start:
{
uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; 
v___x_141_ = 1723ULL;
v___x_142_ = 1ULL;
v___x_143_ = lean_uint64_mix_hash(v___x_142_, v___x_141_);
return v___x_143_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(lean_object* v_x_144_){
_start:
{
switch(lean_obj_tag(v_x_144_))
{
case 0:
{
lean_object* v_fvar_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v___x_148_; 
v_fvar_145_ = lean_ctor_get(v_x_144_, 0);
v___x_146_ = 0ULL;
v___x_147_ = l_Lean_instHashableFVarId_hash(v_fvar_145_);
v___x_148_ = lean_uint64_mix_hash(v___x_146_, v___x_147_);
return v___x_148_;
}
case 1:
{
lean_object* v_n_149_; uint64_t v___x_150_; 
v_n_149_ = lean_ctor_get(v_x_144_, 0);
v___x_150_ = 1ULL;
if (lean_obj_tag(v_n_149_) == 0)
{
uint64_t v___x_151_; 
v___x_151_ = lean_uint64_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___closed__0);
return v___x_151_;
}
else
{
uint64_t v_hash_152_; uint64_t v___x_153_; 
v_hash_152_ = lean_ctor_get_uint64(v_n_149_, sizeof(void*)*2);
v___x_153_ = lean_uint64_mix_hash(v___x_150_, v_hash_152_);
return v___x_153_;
}
}
case 2:
{
lean_object* v_e_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; 
v_e_154_ = lean_ctor_get(v_x_144_, 0);
v___x_155_ = 2ULL;
v___x_156_ = l_Lean_Expr_hash(v_e_154_);
v___x_157_ = lean_uint64_mix_hash(v___x_155_, v___x_156_);
return v___x_157_;
}
default: 
{
lean_object* v_s_158_; uint64_t v___x_159_; uint64_t v___x_160_; uint64_t v___x_161_; 
v_s_158_ = lean_ctor_get(v_x_144_, 0);
v___x_159_ = 3ULL;
v___x_160_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_s_158_);
v___x_161_ = lean_uint64_mix_hash(v___x_159_, v___x_160_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash___boxed(lean_object* v_x_162_){
_start:
{
uint64_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHypSource_hash(v_x_162_);
lean_dec_ref(v_x_162_);
v_r_164_ = lean_box_uint64(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
switch(lean_obj_tag(v_x_167_))
{
case 0:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_object* v_fvar_169_; lean_object* v_fvar_170_; uint8_t v___x_171_; 
v_fvar_169_ = lean_ctor_get(v_x_167_, 0);
v_fvar_170_ = lean_ctor_get(v_x_168_, 0);
v___x_171_ = l_Lean_instBEqFVarId_beq(v_fvar_169_, v_fvar_170_);
return v___x_171_;
}
else
{
uint8_t v___x_172_; 
v___x_172_ = 0;
return v___x_172_;
}
}
case 1:
{
if (lean_obj_tag(v_x_168_) == 1)
{
lean_object* v_n_173_; lean_object* v_n_174_; uint8_t v___x_175_; 
v_n_173_ = lean_ctor_get(v_x_167_, 0);
v_n_174_ = lean_ctor_get(v_x_168_, 0);
v___x_175_ = lean_name_eq(v_n_173_, v_n_174_);
return v___x_175_;
}
else
{
uint8_t v___x_176_; 
v___x_176_ = 0;
return v___x_176_;
}
}
case 2:
{
if (lean_obj_tag(v_x_168_) == 2)
{
lean_object* v_e_177_; lean_object* v_e_178_; uint8_t v___x_179_; 
v_e_177_ = lean_ctor_get(v_x_167_, 0);
v_e_178_ = lean_ctor_get(v_x_168_, 0);
v___x_179_ = lean_expr_eqv(v_e_177_, v_e_178_);
return v___x_179_;
}
else
{
uint8_t v___x_180_; 
v___x_180_ = 0;
return v___x_180_;
}
}
default: 
{
if (lean_obj_tag(v_x_168_) == 3)
{
lean_object* v_s_181_; lean_object* v_s_182_; 
v_s_181_ = lean_ctor_get(v_x_167_, 0);
v_s_182_ = lean_ctor_get(v_x_168_, 0);
v_x_167_ = v_s_181_;
v_x_168_ = v_s_182_;
goto _start;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = 0;
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq___boxed(lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHypSource_beq(v_x_185_, v_x_186_);
lean_dec_ref(v_x_186_);
lean_dec_ref(v_x_185_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(lean_object* v_s_191_){
_start:
{
if (lean_obj_tag(v_s_191_) == 3)
{
lean_object* v_s_192_; 
v_s_192_ = lean_ctor_get(v_s_191_, 0);
v_s_191_ = v_s_192_;
goto _start;
}
else
{
lean_inc_ref(v_s_191_);
return v_s_191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten___boxed(lean_object* v_s_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_194_);
lean_dec_ref(v_s_194_);
return v_res_195_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__0));
v___x_198_ = l_Lean_stringToMessageData(v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__2));
v___x_201_ = l_Lean_stringToMessageData(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__4));
v___x_204_ = l_Lean_stringToMessageData(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__6));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(lean_object* v_s_208_){
_start:
{
switch(lean_obj_tag(v_s_208_))
{
case 0:
{
lean_object* v_fvar_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_fvar_209_ = lean_ctor_get(v_s_208_, 0);
lean_inc(v_fvar_209_);
lean_dec_ref_known(v_s_208_, 1);
v___x_210_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__1);
v___x_211_ = l_Lean_mkFVar(v_fvar_209_);
v___x_212_ = l_Lean_MessageData_ofExpr(v___x_211_);
v___x_213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_210_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
return v___x_213_;
}
case 1:
{
lean_object* v_n_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_n_214_ = lean_ctor_get(v_s_208_, 0);
lean_inc(v_n_214_);
lean_dec_ref_known(v_s_208_, 1);
v___x_215_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__3);
v___x_216_ = l_Lean_MessageData_ofName(v_n_214_);
v___x_217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
case 2:
{
lean_object* v_e_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_e_218_ = lean_ctor_get(v_s_208_, 0);
lean_inc_ref(v_e_218_);
lean_dec_ref_known(v_s_208_, 1);
v___x_219_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__5);
v___x_220_ = l_Lean_MessageData_ofExpr(v_e_218_);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
return v___x_221_;
}
default: 
{
lean_object* v_s_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_s_222_ = lean_ctor_get(v_s_208_, 0);
lean_inc_ref(v_s_222_);
lean_dec_ref_known(v_s_208_, 1);
v___x_223_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go___closed__7);
v___x_224_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_stripFlatten(v_s_222_);
lean_dec_ref(v_s_222_);
v___x_225_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHypSource_go(v___x_224_);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_223_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
return v___x_226_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_box(0);
v___x_233_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__1));
v___x_234_ = l_Lean_Expr_const___override(v___x_233_, v___x_232_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_235_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHypSource_default));
v___x_236_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__2);
v___x_237_ = lean_box(0);
v___x_238_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
lean_ctor_set(v___x_238_, 2, v___x_236_);
lean_ctor_set(v___x_238_, 3, v___x_235_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default(void){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default___closed__3);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp(void){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instInhabitedHyp_default;
return v___x_240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(lean_object* v_lhs_241_, lean_object* v_rhs_242_){
_start:
{
lean_object* v_type_243_; lean_object* v_type_244_; uint8_t v___x_245_; 
v_type_243_ = lean_ctor_get(v_lhs_241_, 1);
v_type_244_ = lean_ctor_get(v_rhs_242_, 1);
v___x_245_ = lean_expr_eqv(v_type_243_, v_type_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0___boxed(lean_object* v_lhs_246_, lean_object* v_rhs_247_){
_start:
{
uint8_t v_res_248_; lean_object* v_r_249_; 
v_res_248_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqHyp___lam__0(v_lhs_246_, v_rhs_247_);
lean_dec_ref(v_rhs_247_);
lean_dec_ref(v_lhs_246_);
v_r_249_ = lean_box(v_res_248_);
return v_r_249_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(lean_object* v_hyp_252_){
_start:
{
lean_object* v_type_253_; uint64_t v___x_254_; 
v_type_253_ = lean_ctor_get(v_hyp_252_, 1);
v___x_254_ = l_Lean_Expr_hash(v_type_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0___boxed(lean_object* v_hyp_255_){
_start:
{
uint64_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instHashableHyp___lam__0(v_hyp_255_);
lean_dec_ref(v_hyp_255_);
v_r_257_ = lean_box_uint64(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instToMessageDataHyp___lam__0(lean_object* v_hyp_260_){
_start:
{
lean_object* v_type_261_; lean_object* v___x_262_; 
v_type_261_ = lean_ctor_get(v_hyp_260_, 1);
lean_inc_ref(v_type_261_);
lean_dec_ref(v_hyp_260_);
v___x_262_ = l_Lean_MessageData_ofExpr(v_type_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object* v_hyp_270_, lean_object* v_result_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
if (lean_obj_tag(v_result_271_) == 0)
{
lean_object* v___x_278_; 
lean_dec_ref_known(v_result_271_, 0);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v_hyp_270_);
return v___x_278_;
}
else
{
lean_object* v_e_x27_279_; lean_object* v_proof_280_; lean_object* v_name_281_; lean_object* v_type_282_; lean_object* v_value_283_; lean_object* v_source_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_313_; 
v_e_x27_279_ = lean_ctor_get(v_result_271_, 0);
lean_inc_ref(v_e_x27_279_);
v_proof_280_ = lean_ctor_get(v_result_271_, 1);
lean_inc_ref(v_proof_280_);
lean_dec_ref_known(v_result_271_, 2);
v_name_281_ = lean_ctor_get(v_hyp_270_, 0);
v_type_282_ = lean_ctor_get(v_hyp_270_, 1);
v_value_283_ = lean_ctor_get(v_hyp_270_, 2);
v_source_284_ = lean_ctor_get(v_hyp_270_, 3);
v_isSharedCheck_313_ = !lean_is_exclusive(v_hyp_270_);
if (v_isSharedCheck_313_ == 0)
{
v___x_286_ = v_hyp_270_;
v_isShared_287_ = v_isSharedCheck_313_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_source_284_);
lean_inc(v_value_283_);
lean_inc(v_type_282_);
lean_inc(v_name_281_);
lean_dec(v_hyp_270_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_313_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; 
lean_inc_ref(v_type_282_);
v___x_288_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_282_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_304_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_304_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_304_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_304_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_293_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___closed__2));
v___x_294_ = lean_box(0);
v___x_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_295_, 0, v_a_289_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = l_Lean_mkConst(v___x_293_, v___x_295_);
lean_inc_ref(v_e_x27_279_);
v___x_297_ = l_Lean_mkApp4(v___x_296_, v_type_282_, v_e_x27_279_, v_proof_280_, v_value_283_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 2, v___x_297_);
lean_ctor_set(v___x_286_, 1, v_e_x27_279_);
v___x_299_ = v___x_286_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_name_281_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_e_x27_279_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_source_284_);
v___x_299_ = v_reuseFailAlloc_303_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_299_);
v___x_301_ = v___x_291_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_del_object(v___x_286_);
lean_dec_ref(v_source_284_);
lean_dec_ref(v_value_283_);
lean_dec_ref(v_type_282_);
lean_dec(v_name_281_);
lean_dec_ref(v_proof_280_);
lean_dec_ref(v_e_x27_279_);
v_a_305_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_288_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_288_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg___boxed(lean_object* v_hyp_314_, lean_object* v_result_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_314_, v_result_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(lean_object* v_hyp_323_, lean_object* v_result_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_323_, v_result_324_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___boxed(lean_object* v_hyp_333_, lean_object* v_result_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult(v_hyp_333_, v_result_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(lean_object* v_hyp_343_, lean_object* v_result_344_){
_start:
{
lean_object* v_name_346_; lean_object* v_type_347_; lean_object* v_value_348_; lean_object* v_source_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_358_; 
v_name_346_ = lean_ctor_get(v_hyp_343_, 0);
v_type_347_ = lean_ctor_get(v_hyp_343_, 1);
v_value_348_ = lean_ctor_get(v_hyp_343_, 2);
v_source_349_ = lean_ctor_get(v_hyp_343_, 3);
v_isSharedCheck_358_ = !lean_is_exclusive(v_hyp_343_);
if (v_isSharedCheck_358_ == 0)
{
v___x_351_ = v_hyp_343_;
v_isShared_352_ = v_isSharedCheck_358_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_source_349_);
lean_inc(v_value_348_);
lean_inc(v_type_347_);
lean_inc(v_name_346_);
lean_dec(v_hyp_343_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_358_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = l_Lean_Meta_Sym_DSimp_Result_getResultExpr(v_type_347_, v_result_344_);
lean_dec_ref(v_type_347_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 1, v___x_353_);
v___x_355_ = v___x_351_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_name_346_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_value_348_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_source_349_);
v___x_355_ = v_reuseFailAlloc_357_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_356_; 
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg___boxed(lean_object* v_hyp_359_, lean_object* v_result_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_359_, v_result_360_);
lean_dec_ref(v_result_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(lean_object* v_hyp_363_, lean_object* v_result_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_363_, v_result_364_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___boxed(lean_object* v_hyp_373_, lean_object* v_result_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult(v_hyp_373_, v_result_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec_ref(v_result_374_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(lean_object* v_a_383_){
_start:
{
lean_object* v___x_385_; 
lean_inc_ref(v_a_383_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v_a_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(v_a_386_);
lean_dec_ref(v_a_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_398_; 
lean_inc_ref(v_a_389_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v_a_389_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___redArg(lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; lean_object* v_goal_412_; lean_object* v___x_413_; 
v___x_411_ = lean_st_ref_get(v_a_409_);
v_goal_412_ = lean_ctor_get(v___x_411_, 4);
lean_inc(v_goal_412_);
lean_dec(v___x_411_);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v_goal_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___redArg___boxed(lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___redArg(v_a_414_);
lean_dec(v_a_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal(lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; lean_object* v_goal_427_; lean_object* v___x_428_; 
v___x_426_ = lean_st_ref_get(v_a_418_);
v_goal_427_ = lean_ctor_get(v___x_426_, 4);
lean_inc(v_goal_427_);
lean_dec(v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v_goal_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___boxed(lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal(v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___redArg(lean_object* v_g_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_442_; lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v_rewriteSimpCache_448_; lean_object* v_rewriteDSimpCache_449_; lean_object* v_acCache_450_; lean_object* v_typeAnalysis_451_; lean_object* v_goal_452_; lean_object* v_hypotheses_453_; uint8_t v_didChange_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_467_; 
v___x_442_ = lean_st_ref_take(v_a_440_);
v_rewriteSimpCache_448_ = lean_ctor_get(v___x_442_, 0);
v_rewriteDSimpCache_449_ = lean_ctor_get(v___x_442_, 1);
v_acCache_450_ = lean_ctor_get(v___x_442_, 2);
v_typeAnalysis_451_ = lean_ctor_get(v___x_442_, 3);
v_goal_452_ = lean_ctor_get(v___x_442_, 4);
v_hypotheses_453_ = lean_ctor_get(v___x_442_, 5);
v_didChange_454_ = lean_ctor_get_uint8(v___x_442_, sizeof(void*)*6);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_467_ == 0)
{
v___x_456_ = v___x_442_;
v_isShared_457_ = v_isSharedCheck_467_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_hypotheses_453_);
lean_inc(v_goal_452_);
lean_inc(v_typeAnalysis_451_);
lean_inc(v_acCache_450_);
lean_inc(v_rewriteDSimpCache_449_);
lean_inc(v_rewriteSimpCache_448_);
lean_dec(v___x_442_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_467_;
goto v_resetjp_455_;
}
v___jp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_st_ref_set(v_a_440_, v_snd_445_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v_fst_444_);
return v___x_447_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; uint8_t v___y_460_; 
v___x_458_ = lean_box(0);
if (v_didChange_454_ == 0)
{
uint8_t v___x_464_; 
v___x_464_ = l_Lean_instBEqMVarId_beq(v_g_439_, v_goal_452_);
lean_dec(v_goal_452_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; 
v___x_465_ = 1;
v___y_460_ = v___x_465_;
goto v___jp_459_;
}
else
{
v___y_460_ = v_didChange_454_;
goto v___jp_459_;
}
}
else
{
lean_object* v___x_466_; 
lean_del_object(v___x_456_);
lean_dec(v_goal_452_);
v___x_466_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_466_, 0, v_rewriteSimpCache_448_);
lean_ctor_set(v___x_466_, 1, v_rewriteDSimpCache_449_);
lean_ctor_set(v___x_466_, 2, v_acCache_450_);
lean_ctor_set(v___x_466_, 3, v_typeAnalysis_451_);
lean_ctor_set(v___x_466_, 4, v_g_439_);
lean_ctor_set(v___x_466_, 5, v_hypotheses_453_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*6, v_didChange_454_);
v_fst_444_ = v___x_458_;
v_snd_445_ = v___x_466_;
goto v___jp_443_;
}
v___jp_459_:
{
lean_object* v___x_462_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 4, v_g_439_);
v___x_462_ = v___x_456_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_rewriteSimpCache_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_rewriteDSimpCache_449_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_acCache_450_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_typeAnalysis_451_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_g_439_);
lean_ctor_set(v_reuseFailAlloc_463_, 5, v_hypotheses_453_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*6, v___y_460_);
v_fst_444_ = v___x_458_;
v_snd_445_ = v___x_462_;
goto v___jp_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___redArg___boxed(lean_object* v_g_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___redArg(v_g_468_, v_a_469_);
lean_dec(v_a_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal(lean_object* v_g_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_482_; lean_object* v_fst_484_; lean_object* v_snd_485_; lean_object* v_rewriteSimpCache_488_; lean_object* v_rewriteDSimpCache_489_; lean_object* v_acCache_490_; lean_object* v_typeAnalysis_491_; lean_object* v_goal_492_; lean_object* v_hypotheses_493_; uint8_t v_didChange_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_507_; 
v___x_482_ = lean_st_ref_take(v_a_474_);
v_rewriteSimpCache_488_ = lean_ctor_get(v___x_482_, 0);
v_rewriteDSimpCache_489_ = lean_ctor_get(v___x_482_, 1);
v_acCache_490_ = lean_ctor_get(v___x_482_, 2);
v_typeAnalysis_491_ = lean_ctor_get(v___x_482_, 3);
v_goal_492_ = lean_ctor_get(v___x_482_, 4);
v_hypotheses_493_ = lean_ctor_get(v___x_482_, 5);
v_didChange_494_ = lean_ctor_get_uint8(v___x_482_, sizeof(void*)*6);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_507_ == 0)
{
v___x_496_ = v___x_482_;
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_hypotheses_493_);
lean_inc(v_goal_492_);
lean_inc(v_typeAnalysis_491_);
lean_inc(v_acCache_490_);
lean_inc(v_rewriteDSimpCache_489_);
lean_inc(v_rewriteSimpCache_488_);
lean_dec(v___x_482_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
v___jp_483_:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_st_ref_set(v_a_474_, v_snd_485_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_fst_484_);
return v___x_487_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; uint8_t v___y_500_; 
v___x_498_ = lean_box(0);
if (v_didChange_494_ == 0)
{
uint8_t v___x_504_; 
v___x_504_ = l_Lean_instBEqMVarId_beq(v_g_472_, v_goal_492_);
lean_dec(v_goal_492_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
v___x_505_ = 1;
v___y_500_ = v___x_505_;
goto v___jp_499_;
}
else
{
v___y_500_ = v_didChange_494_;
goto v___jp_499_;
}
}
else
{
lean_object* v___x_506_; 
lean_del_object(v___x_496_);
lean_dec(v_goal_492_);
v___x_506_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_506_, 0, v_rewriteSimpCache_488_);
lean_ctor_set(v___x_506_, 1, v_rewriteDSimpCache_489_);
lean_ctor_set(v___x_506_, 2, v_acCache_490_);
lean_ctor_set(v___x_506_, 3, v_typeAnalysis_491_);
lean_ctor_set(v___x_506_, 4, v_g_472_);
lean_ctor_set(v___x_506_, 5, v_hypotheses_493_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*6, v_didChange_494_);
v_fst_484_ = v___x_498_;
v_snd_485_ = v___x_506_;
goto v___jp_483_;
}
v___jp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 4, v_g_472_);
v___x_502_ = v___x_496_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_rewriteSimpCache_488_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_rewriteDSimpCache_489_);
lean_ctor_set(v_reuseFailAlloc_503_, 2, v_acCache_490_);
lean_ctor_set(v_reuseFailAlloc_503_, 3, v_typeAnalysis_491_);
lean_ctor_set(v_reuseFailAlloc_503_, 4, v_g_472_);
lean_ctor_set(v_reuseFailAlloc_503_, 5, v_hypotheses_493_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*6, v___y_500_);
v_fst_484_ = v___x_498_;
v_snd_485_ = v___x_502_;
goto v___jp_483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal___boxed(lean_object* v_g_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setGoal(v_g_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(lean_object* v_a_519_){
_start:
{
lean_object* v___x_521_; uint8_t v_didChange_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_521_ = lean_st_ref_get(v_a_519_);
v_didChange_522_ = lean_ctor_get_uint8(v___x_521_, sizeof(void*)*6);
lean_dec(v___x_521_);
v___x_523_ = lean_box(v_didChange_522_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg___boxed(lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___redArg(v_a_525_);
lean_dec(v_a_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_537_; uint8_t v_didChange_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = lean_st_ref_get(v_a_529_);
v_didChange_538_ = lean_ctor_get_uint8(v___x_537_, sizeof(void*)*6);
lean_dec(v___x_537_);
v___x_539_ = lean_box(v_didChange_538_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange___boxed(lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_didChange(v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(lean_object* v_a_551_){
_start:
{
lean_object* v___x_553_; lean_object* v_rewriteSimpCache_554_; lean_object* v_rewriteDSimpCache_555_; lean_object* v_acCache_556_; lean_object* v_typeAnalysis_557_; lean_object* v_goal_558_; lean_object* v_hypotheses_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_570_; 
v___x_553_ = lean_st_ref_take(v_a_551_);
v_rewriteSimpCache_554_ = lean_ctor_get(v___x_553_, 0);
v_rewriteDSimpCache_555_ = lean_ctor_get(v___x_553_, 1);
v_acCache_556_ = lean_ctor_get(v___x_553_, 2);
v_typeAnalysis_557_ = lean_ctor_get(v___x_553_, 3);
v_goal_558_ = lean_ctor_get(v___x_553_, 4);
v_hypotheses_559_ = lean_ctor_get(v___x_553_, 5);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_570_ == 0)
{
v___x_561_ = v___x_553_;
v_isShared_562_ = v_isSharedCheck_570_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_hypotheses_559_);
lean_inc(v_goal_558_);
lean_inc(v_typeAnalysis_557_);
lean_inc(v_acCache_556_);
lean_inc(v_rewriteDSimpCache_555_);
lean_inc(v_rewriteSimpCache_554_);
lean_dec(v___x_553_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_570_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
uint8_t v___x_563_; lean_object* v___x_565_; 
v___x_563_ = 0;
if (v_isShared_562_ == 0)
{
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_rewriteSimpCache_554_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_rewriteDSimpCache_555_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_acCache_556_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_typeAnalysis_557_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_goal_558_);
lean_ctor_set(v_reuseFailAlloc_569_, 5, v_hypotheses_559_);
v___x_565_ = v_reuseFailAlloc_569_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*6, v___x_563_);
v___x_566_ = lean_st_ref_set(v_a_551_, v___x_565_);
v___x_567_ = lean_box(0);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg___boxed(lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___redArg(v_a_571_);
lean_dec(v_a_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v___x_583_; lean_object* v_rewriteSimpCache_584_; lean_object* v_rewriteDSimpCache_585_; lean_object* v_acCache_586_; lean_object* v_typeAnalysis_587_; lean_object* v_goal_588_; lean_object* v_hypotheses_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_600_; 
v___x_583_ = lean_st_ref_take(v_a_575_);
v_rewriteSimpCache_584_ = lean_ctor_get(v___x_583_, 0);
v_rewriteDSimpCache_585_ = lean_ctor_get(v___x_583_, 1);
v_acCache_586_ = lean_ctor_get(v___x_583_, 2);
v_typeAnalysis_587_ = lean_ctor_get(v___x_583_, 3);
v_goal_588_ = lean_ctor_get(v___x_583_, 4);
v_hypotheses_589_ = lean_ctor_get(v___x_583_, 5);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_600_ == 0)
{
v___x_591_ = v___x_583_;
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_hypotheses_589_);
lean_inc(v_goal_588_);
lean_inc(v_typeAnalysis_587_);
lean_inc(v_acCache_586_);
lean_inc(v_rewriteDSimpCache_585_);
lean_inc(v_rewriteSimpCache_584_);
lean_dec(v___x_583_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
uint8_t v___x_593_; lean_object* v___x_595_; 
v___x_593_ = 0;
if (v_isShared_592_ == 0)
{
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_rewriteSimpCache_584_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_rewriteDSimpCache_585_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_acCache_586_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_typeAnalysis_587_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v_goal_588_);
lean_ctor_set(v_reuseFailAlloc_599_, 5, v_hypotheses_589_);
v___x_595_ = v_reuseFailAlloc_599_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*6, v___x_593_);
v___x_596_ = lean_st_ref_set(v_a_575_, v___x_595_);
v___x_597_ = lean_box(0);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange___boxed(lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_resetDidChange(v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(lean_object* v_a_611_){
_start:
{
lean_object* v___x_613_; lean_object* v_rewriteSimpCache_614_; lean_object* v_rewriteDSimpCache_615_; lean_object* v_acCache_616_; lean_object* v_typeAnalysis_617_; lean_object* v_goal_618_; lean_object* v_hypotheses_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_630_; 
v___x_613_ = lean_st_ref_take(v_a_611_);
v_rewriteSimpCache_614_ = lean_ctor_get(v___x_613_, 0);
v_rewriteDSimpCache_615_ = lean_ctor_get(v___x_613_, 1);
v_acCache_616_ = lean_ctor_get(v___x_613_, 2);
v_typeAnalysis_617_ = lean_ctor_get(v___x_613_, 3);
v_goal_618_ = lean_ctor_get(v___x_613_, 4);
v_hypotheses_619_ = lean_ctor_get(v___x_613_, 5);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_630_ == 0)
{
v___x_621_ = v___x_613_;
v_isShared_622_ = v_isSharedCheck_630_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_hypotheses_619_);
lean_inc(v_goal_618_);
lean_inc(v_typeAnalysis_617_);
lean_inc(v_acCache_616_);
lean_inc(v_rewriteDSimpCache_615_);
lean_inc(v_rewriteSimpCache_614_);
lean_dec(v___x_613_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_630_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
uint8_t v___x_623_; lean_object* v___x_625_; 
v___x_623_ = 1;
if (v_isShared_622_ == 0)
{
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_rewriteSimpCache_614_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_rewriteDSimpCache_615_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_acCache_616_);
lean_ctor_set(v_reuseFailAlloc_629_, 3, v_typeAnalysis_617_);
lean_ctor_set(v_reuseFailAlloc_629_, 4, v_goal_618_);
lean_ctor_set(v_reuseFailAlloc_629_, 5, v_hypotheses_619_);
v___x_625_ = v_reuseFailAlloc_629_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*6, v___x_623_);
v___x_626_ = lean_st_ref_set(v_a_611_, v___x_625_);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg___boxed(lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___redArg(v_a_631_);
lean_dec(v_a_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___x_643_; lean_object* v_rewriteSimpCache_644_; lean_object* v_rewriteDSimpCache_645_; lean_object* v_acCache_646_; lean_object* v_typeAnalysis_647_; lean_object* v_goal_648_; lean_object* v_hypotheses_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_660_; 
v___x_643_ = lean_st_ref_take(v_a_635_);
v_rewriteSimpCache_644_ = lean_ctor_get(v___x_643_, 0);
v_rewriteDSimpCache_645_ = lean_ctor_get(v___x_643_, 1);
v_acCache_646_ = lean_ctor_get(v___x_643_, 2);
v_typeAnalysis_647_ = lean_ctor_get(v___x_643_, 3);
v_goal_648_ = lean_ctor_get(v___x_643_, 4);
v_hypotheses_649_ = lean_ctor_get(v___x_643_, 5);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_660_ == 0)
{
v___x_651_ = v___x_643_;
v_isShared_652_ = v_isSharedCheck_660_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_hypotheses_649_);
lean_inc(v_goal_648_);
lean_inc(v_typeAnalysis_647_);
lean_inc(v_acCache_646_);
lean_inc(v_rewriteDSimpCache_645_);
lean_inc(v_rewriteSimpCache_644_);
lean_dec(v___x_643_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_660_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
uint8_t v___x_653_; lean_object* v___x_655_; 
v___x_653_ = 1;
if (v_isShared_652_ == 0)
{
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_rewriteSimpCache_644_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_rewriteDSimpCache_645_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v_acCache_646_);
lean_ctor_set(v_reuseFailAlloc_659_, 3, v_typeAnalysis_647_);
lean_ctor_set(v_reuseFailAlloc_659_, 4, v_goal_648_);
lean_ctor_set(v_reuseFailAlloc_659_, 5, v_hypotheses_649_);
v___x_655_ = v_reuseFailAlloc_659_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*6, v___x_653_);
v___x_656_ = lean_st_ref_set(v_a_635_, v___x_655_);
v___x_657_ = lean_box(0);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed(lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange(v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
return v_res_670_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0(void){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__0);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg(lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; lean_object* v_rewriteSimpCache_677_; lean_object* v_rewriteDSimpCache_678_; lean_object* v_acCache_679_; lean_object* v_typeAnalysis_680_; lean_object* v_goal_681_; lean_object* v_hypotheses_682_; uint8_t v_didChange_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_693_; 
v___x_676_ = lean_st_ref_take(v_a_674_);
v_rewriteSimpCache_677_ = lean_ctor_get(v___x_676_, 0);
v_rewriteDSimpCache_678_ = lean_ctor_get(v___x_676_, 1);
v_acCache_679_ = lean_ctor_get(v___x_676_, 2);
v_typeAnalysis_680_ = lean_ctor_get(v___x_676_, 3);
v_goal_681_ = lean_ctor_get(v___x_676_, 4);
v_hypotheses_682_ = lean_ctor_get(v___x_676_, 5);
v_didChange_683_ = lean_ctor_get_uint8(v___x_676_, sizeof(void*)*6);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_693_ == 0)
{
v___x_685_ = v___x_676_;
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_hypotheses_682_);
lean_inc(v_goal_681_);
lean_inc(v_typeAnalysis_680_);
lean_inc(v_acCache_679_);
lean_inc(v_rewriteDSimpCache_678_);
lean_inc(v_rewriteSimpCache_677_);
lean_dec(v___x_676_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_687_);
v___x_689_ = v___x_685_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_rewriteDSimpCache_678_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_acCache_679_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_typeAnalysis_680_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_goal_681_);
lean_ctor_set(v_reuseFailAlloc_692_, 5, v_hypotheses_682_);
lean_ctor_set_uint8(v_reuseFailAlloc_692_, sizeof(void*)*6, v_didChange_683_);
v___x_689_ = v_reuseFailAlloc_692_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_st_ref_set(v_a_674_, v___x_689_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v_rewriteSimpCache_677_);
return v___x_691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___boxed(lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg(v_a_694_);
lean_dec(v_a_694_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache(lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v___x_706_; lean_object* v_rewriteSimpCache_707_; lean_object* v_rewriteDSimpCache_708_; lean_object* v_acCache_709_; lean_object* v_typeAnalysis_710_; lean_object* v_goal_711_; lean_object* v_hypotheses_712_; uint8_t v_didChange_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_723_; 
v___x_706_ = lean_st_ref_take(v_a_698_);
v_rewriteSimpCache_707_ = lean_ctor_get(v___x_706_, 0);
v_rewriteDSimpCache_708_ = lean_ctor_get(v___x_706_, 1);
v_acCache_709_ = lean_ctor_get(v___x_706_, 2);
v_typeAnalysis_710_ = lean_ctor_get(v___x_706_, 3);
v_goal_711_ = lean_ctor_get(v___x_706_, 4);
v_hypotheses_712_ = lean_ctor_get(v___x_706_, 5);
v_didChange_713_ = lean_ctor_get_uint8(v___x_706_, sizeof(void*)*6);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_723_ == 0)
{
v___x_715_ = v___x_706_;
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_hypotheses_712_);
lean_inc(v_goal_711_);
lean_inc(v_typeAnalysis_710_);
lean_inc(v_acCache_709_);
lean_inc(v_rewriteDSimpCache_708_);
lean_inc(v_rewriteSimpCache_707_);
lean_dec(v___x_706_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_rewriteDSimpCache_708_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_acCache_709_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_typeAnalysis_710_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v_goal_711_);
lean_ctor_set(v_reuseFailAlloc_722_, 5, v_hypotheses_712_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, sizeof(void*)*6, v_didChange_713_);
v___x_719_ = v_reuseFailAlloc_722_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_st_ref_set(v_a_698_, v___x_719_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_rewriteSimpCache_707_);
return v___x_721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___boxed(lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache(v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg(lean_object* v_cache_734_, lean_object* v_a_735_){
_start:
{
lean_object* v___x_737_; lean_object* v_rewriteDSimpCache_738_; lean_object* v_acCache_739_; lean_object* v_typeAnalysis_740_; lean_object* v_goal_741_; lean_object* v_hypotheses_742_; uint8_t v_didChange_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_753_; 
v___x_737_ = lean_st_ref_take(v_a_735_);
v_rewriteDSimpCache_738_ = lean_ctor_get(v___x_737_, 1);
v_acCache_739_ = lean_ctor_get(v___x_737_, 2);
v_typeAnalysis_740_ = lean_ctor_get(v___x_737_, 3);
v_goal_741_ = lean_ctor_get(v___x_737_, 4);
v_hypotheses_742_ = lean_ctor_get(v___x_737_, 5);
v_didChange_743_ = lean_ctor_get_uint8(v___x_737_, sizeof(void*)*6);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_753_ == 0)
{
lean_object* v_unused_754_; 
v_unused_754_ = lean_ctor_get(v___x_737_, 0);
lean_dec(v_unused_754_);
v___x_745_ = v___x_737_;
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_hypotheses_742_);
lean_inc(v_goal_741_);
lean_inc(v_typeAnalysis_740_);
lean_inc(v_acCache_739_);
lean_inc(v_rewriteDSimpCache_738_);
lean_dec(v___x_737_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v_cache_734_);
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_cache_734_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_rewriteDSimpCache_738_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_acCache_739_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_typeAnalysis_740_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v_goal_741_);
lean_ctor_set(v_reuseFailAlloc_752_, 5, v_hypotheses_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*6, v_didChange_743_);
v___x_748_ = v_reuseFailAlloc_752_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = lean_st_ref_set(v_a_735_, v___x_748_);
v___x_750_ = lean_box(0);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg___boxed(lean_object* v_cache_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___redArg(v_cache_755_, v_a_756_);
lean_dec(v_a_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache(lean_object* v_cache_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_769_; lean_object* v_rewriteDSimpCache_770_; lean_object* v_acCache_771_; lean_object* v_typeAnalysis_772_; lean_object* v_goal_773_; lean_object* v_hypotheses_774_; uint8_t v_didChange_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_785_; 
v___x_769_ = lean_st_ref_take(v_a_761_);
v_rewriteDSimpCache_770_ = lean_ctor_get(v___x_769_, 1);
v_acCache_771_ = lean_ctor_get(v___x_769_, 2);
v_typeAnalysis_772_ = lean_ctor_get(v___x_769_, 3);
v_goal_773_ = lean_ctor_get(v___x_769_, 4);
v_hypotheses_774_ = lean_ctor_get(v___x_769_, 5);
v_didChange_775_ = lean_ctor_get_uint8(v___x_769_, sizeof(void*)*6);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v___x_769_, 0);
lean_dec(v_unused_786_);
v___x_777_ = v___x_769_;
v_isShared_778_ = v_isSharedCheck_785_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_hypotheses_774_);
lean_inc(v_goal_773_);
lean_inc(v_typeAnalysis_772_);
lean_inc(v_acCache_771_);
lean_inc(v_rewriteDSimpCache_770_);
lean_dec(v___x_769_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_785_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v_cache_759_);
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_cache_759_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_rewriteDSimpCache_770_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_acCache_771_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_typeAnalysis_772_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_goal_773_);
lean_ctor_set(v_reuseFailAlloc_784_, 5, v_hypotheses_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_784_, sizeof(void*)*6, v_didChange_775_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_st_ref_set(v_a_761_, v___x_780_);
v___x_782_ = lean_box(0);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache___boxed(lean_object* v_cache_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteSimpCache(v_cache_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg(lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; lean_object* v_rewriteDSimpCache_801_; lean_object* v_acCache_802_; lean_object* v_typeAnalysis_803_; lean_object* v_goal_804_; lean_object* v_hypotheses_805_; uint8_t v_didChange_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_817_; 
v___x_800_ = lean_st_ref_take(v_a_798_);
v_rewriteDSimpCache_801_ = lean_ctor_get(v___x_800_, 1);
v_acCache_802_ = lean_ctor_get(v___x_800_, 2);
v_typeAnalysis_803_ = lean_ctor_get(v___x_800_, 3);
v_goal_804_ = lean_ctor_get(v___x_800_, 4);
v_hypotheses_805_ = lean_ctor_get(v___x_800_, 5);
v_didChange_806_ = lean_ctor_get_uint8(v___x_800_, sizeof(void*)*6);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v___x_800_, 0);
lean_dec(v_unused_818_);
v___x_808_ = v___x_800_;
v_isShared_809_ = v_isSharedCheck_817_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_hypotheses_805_);
lean_inc(v_goal_804_);
lean_inc(v_typeAnalysis_803_);
lean_inc(v_acCache_802_);
lean_inc(v_rewriteDSimpCache_801_);
lean_dec(v___x_800_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_817_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_rewriteDSimpCache_801_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_acCache_802_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_typeAnalysis_803_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_goal_804_);
lean_ctor_set(v_reuseFailAlloc_816_, 5, v_hypotheses_805_);
lean_ctor_set_uint8(v_reuseFailAlloc_816_, sizeof(void*)*6, v_didChange_806_);
v___x_812_ = v_reuseFailAlloc_816_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = lean_st_ref_set(v_a_798_, v___x_812_);
v___x_814_ = lean_box(0);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg___boxed(lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___redArg(v_a_819_);
lean_dec(v_a_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache(lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v___x_831_; lean_object* v_rewriteDSimpCache_832_; lean_object* v_acCache_833_; lean_object* v_typeAnalysis_834_; lean_object* v_goal_835_; lean_object* v_hypotheses_836_; uint8_t v_didChange_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_848_; 
v___x_831_ = lean_st_ref_take(v_a_823_);
v_rewriteDSimpCache_832_ = lean_ctor_get(v___x_831_, 1);
v_acCache_833_ = lean_ctor_get(v___x_831_, 2);
v_typeAnalysis_834_ = lean_ctor_get(v___x_831_, 3);
v_goal_835_ = lean_ctor_get(v___x_831_, 4);
v_hypotheses_836_ = lean_ctor_get(v___x_831_, 5);
v_didChange_837_ = lean_ctor_get_uint8(v___x_831_, sizeof(void*)*6);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v___x_831_, 0);
lean_dec(v_unused_849_);
v___x_839_ = v___x_831_;
v_isShared_840_ = v_isSharedCheck_848_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_hypotheses_836_);
lean_inc(v_goal_835_);
lean_inc(v_typeAnalysis_834_);
lean_inc(v_acCache_833_);
lean_inc(v_rewriteDSimpCache_832_);
lean_dec(v___x_831_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_848_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_841_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_rewriteDSimpCache_832_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v_acCache_833_);
lean_ctor_set(v_reuseFailAlloc_847_, 3, v_typeAnalysis_834_);
lean_ctor_set(v_reuseFailAlloc_847_, 4, v_goal_835_);
lean_ctor_set(v_reuseFailAlloc_847_, 5, v_hypotheses_836_);
lean_ctor_set_uint8(v_reuseFailAlloc_847_, sizeof(void*)*6, v_didChange_837_);
v___x_843_ = v_reuseFailAlloc_847_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_st_ref_set(v_a_823_, v___x_843_);
v___x_845_ = lean_box(0);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache___boxed(lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteSimpCache(v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
return v_res_859_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0(void){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__0);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg(lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; lean_object* v_rewriteSimpCache_866_; lean_object* v_rewriteDSimpCache_867_; lean_object* v_acCache_868_; lean_object* v_typeAnalysis_869_; lean_object* v_goal_870_; lean_object* v_hypotheses_871_; uint8_t v_didChange_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_882_; 
v___x_865_ = lean_st_ref_take(v_a_863_);
v_rewriteSimpCache_866_ = lean_ctor_get(v___x_865_, 0);
v_rewriteDSimpCache_867_ = lean_ctor_get(v___x_865_, 1);
v_acCache_868_ = lean_ctor_get(v___x_865_, 2);
v_typeAnalysis_869_ = lean_ctor_get(v___x_865_, 3);
v_goal_870_ = lean_ctor_get(v___x_865_, 4);
v_hypotheses_871_ = lean_ctor_get(v___x_865_, 5);
v_didChange_872_ = lean_ctor_get_uint8(v___x_865_, sizeof(void*)*6);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_882_ == 0)
{
v___x_874_ = v___x_865_;
v_isShared_875_ = v_isSharedCheck_882_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_hypotheses_871_);
lean_inc(v_goal_870_);
lean_inc(v_typeAnalysis_869_);
lean_inc(v_acCache_868_);
lean_inc(v_rewriteDSimpCache_867_);
lean_inc(v_rewriteSimpCache_866_);
lean_dec(v___x_865_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_882_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v___x_876_);
v___x_878_ = v___x_874_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_rewriteSimpCache_866_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_acCache_868_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v_typeAnalysis_869_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v_goal_870_);
lean_ctor_set(v_reuseFailAlloc_881_, 5, v_hypotheses_871_);
lean_ctor_set_uint8(v_reuseFailAlloc_881_, sizeof(void*)*6, v_didChange_872_);
v___x_878_ = v_reuseFailAlloc_881_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_st_ref_set(v_a_863_, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v_rewriteDSimpCache_867_);
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___boxed(lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg(v_a_883_);
lean_dec(v_a_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache(lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v___x_895_; lean_object* v_rewriteSimpCache_896_; lean_object* v_rewriteDSimpCache_897_; lean_object* v_acCache_898_; lean_object* v_typeAnalysis_899_; lean_object* v_goal_900_; lean_object* v_hypotheses_901_; uint8_t v_didChange_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
v___x_895_ = lean_st_ref_take(v_a_887_);
v_rewriteSimpCache_896_ = lean_ctor_get(v___x_895_, 0);
v_rewriteDSimpCache_897_ = lean_ctor_get(v___x_895_, 1);
v_acCache_898_ = lean_ctor_get(v___x_895_, 2);
v_typeAnalysis_899_ = lean_ctor_get(v___x_895_, 3);
v_goal_900_ = lean_ctor_get(v___x_895_, 4);
v_hypotheses_901_ = lean_ctor_get(v___x_895_, 5);
v_didChange_902_ = lean_ctor_get_uint8(v___x_895_, sizeof(void*)*6);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_912_ == 0)
{
v___x_904_ = v___x_895_;
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_hypotheses_901_);
lean_inc(v_goal_900_);
lean_inc(v_typeAnalysis_899_);
lean_inc(v_acCache_898_);
lean_inc(v_rewriteDSimpCache_897_);
lean_inc(v_rewriteSimpCache_896_);
lean_dec(v___x_895_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v___x_906_);
v___x_908_ = v___x_904_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_rewriteSimpCache_896_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_acCache_898_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v_typeAnalysis_899_);
lean_ctor_set(v_reuseFailAlloc_911_, 4, v_goal_900_);
lean_ctor_set(v_reuseFailAlloc_911_, 5, v_hypotheses_901_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, sizeof(void*)*6, v_didChange_902_);
v___x_908_ = v_reuseFailAlloc_911_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_st_ref_set(v_a_887_, v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v_rewriteDSimpCache_897_);
return v___x_910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___boxed(lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache(v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg(lean_object* v_cache_923_, lean_object* v_a_924_){
_start:
{
lean_object* v___x_926_; lean_object* v_rewriteSimpCache_927_; lean_object* v_acCache_928_; lean_object* v_typeAnalysis_929_; lean_object* v_goal_930_; lean_object* v_hypotheses_931_; uint8_t v_didChange_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_942_; 
v___x_926_ = lean_st_ref_take(v_a_924_);
v_rewriteSimpCache_927_ = lean_ctor_get(v___x_926_, 0);
v_acCache_928_ = lean_ctor_get(v___x_926_, 2);
v_typeAnalysis_929_ = lean_ctor_get(v___x_926_, 3);
v_goal_930_ = lean_ctor_get(v___x_926_, 4);
v_hypotheses_931_ = lean_ctor_get(v___x_926_, 5);
v_didChange_932_ = lean_ctor_get_uint8(v___x_926_, sizeof(void*)*6);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v___x_926_, 1);
lean_dec(v_unused_943_);
v___x_934_ = v___x_926_;
v_isShared_935_ = v_isSharedCheck_942_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_hypotheses_931_);
lean_inc(v_goal_930_);
lean_inc(v_typeAnalysis_929_);
lean_inc(v_acCache_928_);
lean_inc(v_rewriteSimpCache_927_);
lean_dec(v___x_926_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_942_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 1, v_cache_923_);
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_rewriteSimpCache_927_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_cache_923_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_acCache_928_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_typeAnalysis_929_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_goal_930_);
lean_ctor_set(v_reuseFailAlloc_941_, 5, v_hypotheses_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_941_, sizeof(void*)*6, v_didChange_932_);
v___x_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = lean_st_ref_set(v_a_924_, v___x_937_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg___boxed(lean_object* v_cache_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___redArg(v_cache_944_, v_a_945_);
lean_dec(v_a_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache(lean_object* v_cache_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_958_; lean_object* v_rewriteSimpCache_959_; lean_object* v_acCache_960_; lean_object* v_typeAnalysis_961_; lean_object* v_goal_962_; lean_object* v_hypotheses_963_; uint8_t v_didChange_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_974_; 
v___x_958_ = lean_st_ref_take(v_a_950_);
v_rewriteSimpCache_959_ = lean_ctor_get(v___x_958_, 0);
v_acCache_960_ = lean_ctor_get(v___x_958_, 2);
v_typeAnalysis_961_ = lean_ctor_get(v___x_958_, 3);
v_goal_962_ = lean_ctor_get(v___x_958_, 4);
v_hypotheses_963_ = lean_ctor_get(v___x_958_, 5);
v_didChange_964_ = lean_ctor_get_uint8(v___x_958_, sizeof(void*)*6);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v___x_958_, 1);
lean_dec(v_unused_975_);
v___x_966_ = v___x_958_;
v_isShared_967_ = v_isSharedCheck_974_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_hypotheses_963_);
lean_inc(v_goal_962_);
lean_inc(v_typeAnalysis_961_);
lean_inc(v_acCache_960_);
lean_inc(v_rewriteSimpCache_959_);
lean_dec(v___x_958_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_974_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 1, v_cache_948_);
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_rewriteSimpCache_959_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_cache_948_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v_acCache_960_);
lean_ctor_set(v_reuseFailAlloc_973_, 3, v_typeAnalysis_961_);
lean_ctor_set(v_reuseFailAlloc_973_, 4, v_goal_962_);
lean_ctor_set(v_reuseFailAlloc_973_, 5, v_hypotheses_963_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*6, v_didChange_964_);
v___x_969_ = v_reuseFailAlloc_973_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = lean_st_ref_set(v_a_950_, v___x_969_);
v___x_971_ = lean_box(0);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache___boxed(lean_object* v_cache_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setRewriteDSimpCache(v_cache_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg(lean_object* v_a_987_){
_start:
{
lean_object* v___x_989_; lean_object* v_rewriteSimpCache_990_; lean_object* v_acCache_991_; lean_object* v_typeAnalysis_992_; lean_object* v_goal_993_; lean_object* v_hypotheses_994_; uint8_t v_didChange_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1006_; 
v___x_989_ = lean_st_ref_take(v_a_987_);
v_rewriteSimpCache_990_ = lean_ctor_get(v___x_989_, 0);
v_acCache_991_ = lean_ctor_get(v___x_989_, 2);
v_typeAnalysis_992_ = lean_ctor_get(v___x_989_, 3);
v_goal_993_ = lean_ctor_get(v___x_989_, 4);
v_hypotheses_994_ = lean_ctor_get(v___x_989_, 5);
v_didChange_995_ = lean_ctor_get_uint8(v___x_989_, sizeof(void*)*6);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; 
v_unused_1007_ = lean_ctor_get(v___x_989_, 1);
lean_dec(v_unused_1007_);
v___x_997_ = v___x_989_;
v_isShared_998_ = v_isSharedCheck_1006_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_hypotheses_994_);
lean_inc(v_goal_993_);
lean_inc(v_typeAnalysis_992_);
lean_inc(v_acCache_991_);
lean_inc(v_rewriteSimpCache_990_);
lean_dec(v___x_989_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1006_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_999_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_rewriteSimpCache_990_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_acCache_991_);
lean_ctor_set(v_reuseFailAlloc_1005_, 3, v_typeAnalysis_992_);
lean_ctor_set(v_reuseFailAlloc_1005_, 4, v_goal_993_);
lean_ctor_set(v_reuseFailAlloc_1005_, 5, v_hypotheses_994_);
lean_ctor_set_uint8(v_reuseFailAlloc_1005_, sizeof(void*)*6, v_didChange_995_);
v___x_1001_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_st_ref_set(v_a_987_, v___x_1001_);
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg___boxed(lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___redArg(v_a_1008_);
lean_dec(v_a_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache(lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1020_; lean_object* v_rewriteSimpCache_1021_; lean_object* v_acCache_1022_; lean_object* v_typeAnalysis_1023_; lean_object* v_goal_1024_; lean_object* v_hypotheses_1025_; uint8_t v_didChange_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1037_; 
v___x_1020_ = lean_st_ref_take(v_a_1012_);
v_rewriteSimpCache_1021_ = lean_ctor_get(v___x_1020_, 0);
v_acCache_1022_ = lean_ctor_get(v___x_1020_, 2);
v_typeAnalysis_1023_ = lean_ctor_get(v___x_1020_, 3);
v_goal_1024_ = lean_ctor_get(v___x_1020_, 4);
v_hypotheses_1025_ = lean_ctor_get(v___x_1020_, 5);
v_didChange_1026_ = lean_ctor_get_uint8(v___x_1020_, sizeof(void*)*6);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v___x_1020_, 1);
lean_dec(v_unused_1038_);
v___x_1028_ = v___x_1020_;
v_isShared_1029_ = v_isSharedCheck_1037_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_hypotheses_1025_);
lean_inc(v_goal_1024_);
lean_inc(v_typeAnalysis_1023_);
lean_inc(v_acCache_1022_);
lean_inc(v_rewriteSimpCache_1021_);
lean_dec(v___x_1020_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1037_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v___x_1030_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_rewriteSimpCache_1021_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1036_, 2, v_acCache_1022_);
lean_ctor_set(v_reuseFailAlloc_1036_, 3, v_typeAnalysis_1023_);
lean_ctor_set(v_reuseFailAlloc_1036_, 4, v_goal_1024_);
lean_ctor_set(v_reuseFailAlloc_1036_, 5, v_hypotheses_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*6, v_didChange_1026_);
v___x_1032_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = lean_st_ref_set(v_a_1012_, v___x_1032_);
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache___boxed(lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropRewriteDSimpCache(v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg(lean_object* v_a_1049_){
_start:
{
lean_object* v___x_1051_; lean_object* v_rewriteSimpCache_1052_; lean_object* v_rewriteDSimpCache_1053_; lean_object* v_acCache_1054_; lean_object* v_typeAnalysis_1055_; lean_object* v_goal_1056_; lean_object* v_hypotheses_1057_; uint8_t v_didChange_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1068_; 
v___x_1051_ = lean_st_ref_take(v_a_1049_);
v_rewriteSimpCache_1052_ = lean_ctor_get(v___x_1051_, 0);
v_rewriteDSimpCache_1053_ = lean_ctor_get(v___x_1051_, 1);
v_acCache_1054_ = lean_ctor_get(v___x_1051_, 2);
v_typeAnalysis_1055_ = lean_ctor_get(v___x_1051_, 3);
v_goal_1056_ = lean_ctor_get(v___x_1051_, 4);
v_hypotheses_1057_ = lean_ctor_get(v___x_1051_, 5);
v_didChange_1058_ = lean_ctor_get_uint8(v___x_1051_, sizeof(void*)*6);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1060_ = v___x_1051_;
v_isShared_1061_ = v_isSharedCheck_1068_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_hypotheses_1057_);
lean_inc(v_goal_1056_);
lean_inc(v_typeAnalysis_1055_);
lean_inc(v_acCache_1054_);
lean_inc(v_rewriteDSimpCache_1053_);
lean_inc(v_rewriteSimpCache_1052_);
lean_dec(v___x_1051_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1068_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1062_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 2, v___x_1062_);
v___x_1064_ = v___x_1060_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_rewriteSimpCache_1052_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_rewriteDSimpCache_1053_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_typeAnalysis_1055_);
lean_ctor_set(v_reuseFailAlloc_1067_, 4, v_goal_1056_);
lean_ctor_set(v_reuseFailAlloc_1067_, 5, v_hypotheses_1057_);
lean_ctor_set_uint8(v_reuseFailAlloc_1067_, sizeof(void*)*6, v_didChange_1058_);
v___x_1064_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_st_ref_set(v_a_1049_, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_acCache_1054_);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg___boxed(lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___redArg(v_a_1069_);
lean_dec(v_a_1069_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache(lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v___x_1081_; lean_object* v_rewriteSimpCache_1082_; lean_object* v_rewriteDSimpCache_1083_; lean_object* v_acCache_1084_; lean_object* v_typeAnalysis_1085_; lean_object* v_goal_1086_; lean_object* v_hypotheses_1087_; uint8_t v_didChange_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1098_; 
v___x_1081_ = lean_st_ref_take(v_a_1073_);
v_rewriteSimpCache_1082_ = lean_ctor_get(v___x_1081_, 0);
v_rewriteDSimpCache_1083_ = lean_ctor_get(v___x_1081_, 1);
v_acCache_1084_ = lean_ctor_get(v___x_1081_, 2);
v_typeAnalysis_1085_ = lean_ctor_get(v___x_1081_, 3);
v_goal_1086_ = lean_ctor_get(v___x_1081_, 4);
v_hypotheses_1087_ = lean_ctor_get(v___x_1081_, 5);
v_didChange_1088_ = lean_ctor_get_uint8(v___x_1081_, sizeof(void*)*6);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1090_ = v___x_1081_;
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_hypotheses_1087_);
lean_inc(v_goal_1086_);
lean_inc(v_typeAnalysis_1085_);
lean_inc(v_acCache_1084_);
lean_inc(v_rewriteDSimpCache_1083_);
lean_inc(v_rewriteSimpCache_1082_);
lean_dec(v___x_1081_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 2, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_rewriteSimpCache_1082_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_rewriteDSimpCache_1083_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_typeAnalysis_1085_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_goal_1086_);
lean_ctor_set(v_reuseFailAlloc_1097_, 5, v_hypotheses_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1097_, sizeof(void*)*6, v_didChange_1088_);
v___x_1094_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_st_ref_set(v_a_1073_, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_acCache_1084_);
return v___x_1096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache___boxed(lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeACCache(v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg(lean_object* v_cache_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___x_1112_; lean_object* v_rewriteSimpCache_1113_; lean_object* v_rewriteDSimpCache_1114_; lean_object* v_typeAnalysis_1115_; lean_object* v_goal_1116_; lean_object* v_hypotheses_1117_; uint8_t v_didChange_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1128_; 
v___x_1112_ = lean_st_ref_take(v_a_1110_);
v_rewriteSimpCache_1113_ = lean_ctor_get(v___x_1112_, 0);
v_rewriteDSimpCache_1114_ = lean_ctor_get(v___x_1112_, 1);
v_typeAnalysis_1115_ = lean_ctor_get(v___x_1112_, 3);
v_goal_1116_ = lean_ctor_get(v___x_1112_, 4);
v_hypotheses_1117_ = lean_ctor_get(v___x_1112_, 5);
v_didChange_1118_ = lean_ctor_get_uint8(v___x_1112_, sizeof(void*)*6);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v___x_1112_, 2);
lean_dec(v_unused_1129_);
v___x_1120_ = v___x_1112_;
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_hypotheses_1117_);
lean_inc(v_goal_1116_);
lean_inc(v_typeAnalysis_1115_);
lean_inc(v_rewriteDSimpCache_1114_);
lean_inc(v_rewriteSimpCache_1113_);
lean_dec(v___x_1112_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 2, v_cache_1109_);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_rewriteSimpCache_1113_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_rewriteDSimpCache_1114_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_cache_1109_);
lean_ctor_set(v_reuseFailAlloc_1127_, 3, v_typeAnalysis_1115_);
lean_ctor_set(v_reuseFailAlloc_1127_, 4, v_goal_1116_);
lean_ctor_set(v_reuseFailAlloc_1127_, 5, v_hypotheses_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1127_, sizeof(void*)*6, v_didChange_1118_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = lean_st_ref_set(v_a_1110_, v___x_1123_);
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg___boxed(lean_object* v_cache_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___redArg(v_cache_1130_, v_a_1131_);
lean_dec(v_a_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache(lean_object* v_cache_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v_rewriteSimpCache_1145_; lean_object* v_rewriteDSimpCache_1146_; lean_object* v_typeAnalysis_1147_; lean_object* v_goal_1148_; lean_object* v_hypotheses_1149_; uint8_t v_didChange_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1160_; 
v___x_1144_ = lean_st_ref_take(v_a_1136_);
v_rewriteSimpCache_1145_ = lean_ctor_get(v___x_1144_, 0);
v_rewriteDSimpCache_1146_ = lean_ctor_get(v___x_1144_, 1);
v_typeAnalysis_1147_ = lean_ctor_get(v___x_1144_, 3);
v_goal_1148_ = lean_ctor_get(v___x_1144_, 4);
v_hypotheses_1149_ = lean_ctor_get(v___x_1144_, 5);
v_didChange_1150_ = lean_ctor_get_uint8(v___x_1144_, sizeof(void*)*6);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v___x_1144_, 2);
lean_dec(v_unused_1161_);
v___x_1152_ = v___x_1144_;
v_isShared_1153_ = v_isSharedCheck_1160_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_hypotheses_1149_);
lean_inc(v_goal_1148_);
lean_inc(v_typeAnalysis_1147_);
lean_inc(v_rewriteDSimpCache_1146_);
lean_inc(v_rewriteSimpCache_1145_);
lean_dec(v___x_1144_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1160_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 2, v_cache_1134_);
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_rewriteSimpCache_1145_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_rewriteDSimpCache_1146_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_cache_1134_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_typeAnalysis_1147_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_goal_1148_);
lean_ctor_set(v_reuseFailAlloc_1159_, 5, v_hypotheses_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1159_, sizeof(void*)*6, v_didChange_1150_);
v___x_1155_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_st_ref_set(v_a_1136_, v___x_1155_);
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache___boxed(lean_object* v_cache_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setACCache(v_cache_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg(lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v_rewriteSimpCache_1176_; lean_object* v_rewriteDSimpCache_1177_; lean_object* v_typeAnalysis_1178_; lean_object* v_goal_1179_; lean_object* v_hypotheses_1180_; uint8_t v_didChange_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1192_; 
v___x_1175_ = lean_st_ref_take(v_a_1173_);
v_rewriteSimpCache_1176_ = lean_ctor_get(v___x_1175_, 0);
v_rewriteDSimpCache_1177_ = lean_ctor_get(v___x_1175_, 1);
v_typeAnalysis_1178_ = lean_ctor_get(v___x_1175_, 3);
v_goal_1179_ = lean_ctor_get(v___x_1175_, 4);
v_hypotheses_1180_ = lean_ctor_get(v___x_1175_, 5);
v_didChange_1181_ = lean_ctor_get_uint8(v___x_1175_, sizeof(void*)*6);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v___x_1175_, 2);
lean_dec(v_unused_1193_);
v___x_1183_ = v___x_1175_;
v_isShared_1184_ = v_isSharedCheck_1192_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_hypotheses_1180_);
lean_inc(v_goal_1179_);
lean_inc(v_typeAnalysis_1178_);
lean_inc(v_rewriteDSimpCache_1177_);
lean_inc(v_rewriteSimpCache_1176_);
lean_dec(v___x_1175_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1192_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1185_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 2, v___x_1185_);
v___x_1187_ = v___x_1183_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_rewriteSimpCache_1176_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_rewriteDSimpCache_1177_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v_typeAnalysis_1178_);
lean_ctor_set(v_reuseFailAlloc_1191_, 4, v_goal_1179_);
lean_ctor_set(v_reuseFailAlloc_1191_, 5, v_hypotheses_1180_);
lean_ctor_set_uint8(v_reuseFailAlloc_1191_, sizeof(void*)*6, v_didChange_1181_);
v___x_1187_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = lean_st_ref_set(v_a_1173_, v___x_1187_);
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg___boxed(lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___redArg(v_a_1194_);
lean_dec(v_a_1194_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache(lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v___x_1206_; lean_object* v_rewriteSimpCache_1207_; lean_object* v_rewriteDSimpCache_1208_; lean_object* v_typeAnalysis_1209_; lean_object* v_goal_1210_; lean_object* v_hypotheses_1211_; uint8_t v_didChange_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1223_; 
v___x_1206_ = lean_st_ref_take(v_a_1198_);
v_rewriteSimpCache_1207_ = lean_ctor_get(v___x_1206_, 0);
v_rewriteDSimpCache_1208_ = lean_ctor_get(v___x_1206_, 1);
v_typeAnalysis_1209_ = lean_ctor_get(v___x_1206_, 3);
v_goal_1210_ = lean_ctor_get(v___x_1206_, 4);
v_hypotheses_1211_ = lean_ctor_get(v___x_1206_, 5);
v_didChange_1212_ = lean_ctor_get_uint8(v___x_1206_, sizeof(void*)*6);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v___x_1206_, 2);
lean_dec(v_unused_1224_);
v___x_1214_ = v___x_1206_;
v_isShared_1215_ = v_isSharedCheck_1223_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_hypotheses_1211_);
lean_inc(v_goal_1210_);
lean_inc(v_typeAnalysis_1209_);
lean_inc(v_rewriteDSimpCache_1208_);
lean_inc(v_rewriteSimpCache_1207_);
lean_dec(v___x_1206_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1223_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 2, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_rewriteSimpCache_1207_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_rewriteDSimpCache_1208_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_typeAnalysis_1209_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_goal_1210_);
lean_ctor_set(v_reuseFailAlloc_1222_, 5, v_hypotheses_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*6, v_didChange_1212_);
v___x_1218_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_st_ref_set(v_a_1198_, v___x_1218_);
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache___boxed(lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropACCache(v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(lean_object* v_a_1235_){
_start:
{
lean_object* v___x_1237_; lean_object* v_rewriteDSimpCache_1238_; lean_object* v_acCache_1239_; lean_object* v_typeAnalysis_1240_; lean_object* v_goal_1241_; lean_object* v_hypotheses_1242_; uint8_t v_didChange_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1286_; 
v___x_1237_ = lean_st_ref_take(v_a_1235_);
v_rewriteDSimpCache_1238_ = lean_ctor_get(v___x_1237_, 1);
v_acCache_1239_ = lean_ctor_get(v___x_1237_, 2);
v_typeAnalysis_1240_ = lean_ctor_get(v___x_1237_, 3);
v_goal_1241_ = lean_ctor_get(v___x_1237_, 4);
v_hypotheses_1242_ = lean_ctor_get(v___x_1237_, 5);
v_didChange_1243_ = lean_ctor_get_uint8(v___x_1237_, sizeof(void*)*6);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v___x_1237_, 0);
lean_dec(v_unused_1287_);
v___x_1245_ = v___x_1237_;
v_isShared_1246_ = v_isSharedCheck_1286_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_hypotheses_1242_);
lean_inc(v_goal_1241_);
lean_inc(v_typeAnalysis_1240_);
lean_inc(v_acCache_1239_);
lean_inc(v_rewriteDSimpCache_1238_);
lean_dec(v___x_1237_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1286_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1247_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1247_);
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_rewriteDSimpCache_1238_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v_acCache_1239_);
lean_ctor_set(v_reuseFailAlloc_1285_, 3, v_typeAnalysis_1240_);
lean_ctor_set(v_reuseFailAlloc_1285_, 4, v_goal_1241_);
lean_ctor_set(v_reuseFailAlloc_1285_, 5, v_hypotheses_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1285_, sizeof(void*)*6, v_didChange_1243_);
v___x_1249_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_rewriteSimpCache_1252_; lean_object* v_acCache_1253_; lean_object* v_typeAnalysis_1254_; lean_object* v_goal_1255_; lean_object* v_hypotheses_1256_; uint8_t v_didChange_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1283_; 
v___x_1250_ = lean_st_ref_set(v_a_1235_, v___x_1249_);
v___x_1251_ = lean_st_ref_take(v_a_1235_);
v_rewriteSimpCache_1252_ = lean_ctor_get(v___x_1251_, 0);
v_acCache_1253_ = lean_ctor_get(v___x_1251_, 2);
v_typeAnalysis_1254_ = lean_ctor_get(v___x_1251_, 3);
v_goal_1255_ = lean_ctor_get(v___x_1251_, 4);
v_hypotheses_1256_ = lean_ctor_get(v___x_1251_, 5);
v_didChange_1257_ = lean_ctor_get_uint8(v___x_1251_, sizeof(void*)*6);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v___x_1251_, 1);
lean_dec(v_unused_1284_);
v___x_1259_ = v___x_1251_;
v_isShared_1260_ = v_isSharedCheck_1283_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_hypotheses_1256_);
lean_inc(v_goal_1255_);
lean_inc(v_typeAnalysis_1254_);
lean_inc(v_acCache_1253_);
lean_inc(v_rewriteSimpCache_1252_);
lean_dec(v___x_1251_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1283_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v___x_1247_);
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_rewriteSimpCache_1252_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_acCache_1253_);
lean_ctor_set(v_reuseFailAlloc_1282_, 3, v_typeAnalysis_1254_);
lean_ctor_set(v_reuseFailAlloc_1282_, 4, v_goal_1255_);
lean_ctor_set(v_reuseFailAlloc_1282_, 5, v_hypotheses_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1282_, sizeof(void*)*6, v_didChange_1257_);
v___x_1262_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v_rewriteSimpCache_1265_; lean_object* v_rewriteDSimpCache_1266_; lean_object* v_typeAnalysis_1267_; lean_object* v_goal_1268_; lean_object* v_hypotheses_1269_; uint8_t v_didChange_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1280_; 
v___x_1263_ = lean_st_ref_set(v_a_1235_, v___x_1262_);
v___x_1264_ = lean_st_ref_take(v_a_1235_);
v_rewriteSimpCache_1265_ = lean_ctor_get(v___x_1264_, 0);
v_rewriteDSimpCache_1266_ = lean_ctor_get(v___x_1264_, 1);
v_typeAnalysis_1267_ = lean_ctor_get(v___x_1264_, 3);
v_goal_1268_ = lean_ctor_get(v___x_1264_, 4);
v_hypotheses_1269_ = lean_ctor_get(v___x_1264_, 5);
v_didChange_1270_ = lean_ctor_get_uint8(v___x_1264_, sizeof(void*)*6);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v___x_1264_, 2);
lean_dec(v_unused_1281_);
v___x_1272_ = v___x_1264_;
v_isShared_1273_ = v_isSharedCheck_1280_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_hypotheses_1269_);
lean_inc(v_goal_1268_);
lean_inc(v_typeAnalysis_1267_);
lean_inc(v_rewriteDSimpCache_1266_);
lean_inc(v_rewriteSimpCache_1265_);
lean_dec(v___x_1264_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1280_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 2, v___x_1247_);
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_rewriteSimpCache_1265_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_rewriteDSimpCache_1266_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v_typeAnalysis_1267_);
lean_ctor_set(v_reuseFailAlloc_1279_, 4, v_goal_1268_);
lean_ctor_set(v_reuseFailAlloc_1279_, 5, v_hypotheses_1269_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*6, v_didChange_1270_);
v___x_1275_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = lean_st_ref_set(v_a_1235_, v___x_1275_);
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg___boxed(lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(v_a_1288_);
lean_dec(v_a_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches(lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(v_a_1292_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___boxed(lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches(v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v_typeAnalysis_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_st_ref_get(v_a_1311_);
v_typeAnalysis_1314_ = lean_ctor_get(v___x_1313_, 3);
lean_inc_ref(v_typeAnalysis_1314_);
lean_dec(v___x_1313_);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_typeAnalysis_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_1316_);
lean_dec(v_a_1316_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v___x_1328_; lean_object* v_typeAnalysis_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_st_ref_get(v_a_1320_);
v_typeAnalysis_1329_ = lean_ctor_get(v___x_1328_, 3);
lean_inc_ref(v_typeAnalysis_1329_);
lean_dec(v___x_1328_);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v_typeAnalysis_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(lean_object* v_n_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v_typeAnalysis_1350_; lean_object* v_interestingStructures_1351_; lean_object* v_uninteresting_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1349_ = lean_st_ref_get(v_a_1347_);
v_typeAnalysis_1350_ = lean_ctor_get(v___x_1349_, 3);
lean_inc_ref(v_typeAnalysis_1350_);
lean_dec(v___x_1349_);
v_interestingStructures_1351_ = lean_ctor_get(v_typeAnalysis_1350_, 0);
lean_inc_ref(v_interestingStructures_1351_);
v_uninteresting_1352_ = lean_ctor_get(v_typeAnalysis_1350_, 3);
lean_inc_ref(v_uninteresting_1352_);
lean_dec_ref(v_typeAnalysis_1350_);
v___x_1353_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1354_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
lean_inc(v_n_1346_);
v___x_1355_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1353_, v___x_1354_, v_uninteresting_1352_, v_n_1346_);
lean_dec_ref(v_uninteresting_1352_);
if (v___x_1355_ == 0)
{
uint8_t v___x_1356_; 
v___x_1356_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1353_, v___x_1354_, v_interestingStructures_1351_, v_n_1346_);
lean_dec_ref(v_interestingStructures_1351_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_box(0);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = lean_box(v___x_1356_);
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec_ref(v_interestingStructures_1351_);
lean_dec(v_n_1346_);
v___x_1362_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(lean_object* v_n_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(v_n_1364_, v_a_1365_);
lean_dec(v_a_1365_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(lean_object* v_n_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v___x_1378_; lean_object* v_typeAnalysis_1379_; lean_object* v_interestingStructures_1380_; lean_object* v_uninteresting_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1378_ = lean_st_ref_get(v_a_1370_);
v_typeAnalysis_1379_ = lean_ctor_get(v___x_1378_, 3);
lean_inc_ref(v_typeAnalysis_1379_);
lean_dec(v___x_1378_);
v_interestingStructures_1380_ = lean_ctor_get(v_typeAnalysis_1379_, 0);
lean_inc_ref(v_interestingStructures_1380_);
v_uninteresting_1381_ = lean_ctor_get(v_typeAnalysis_1379_, 3);
lean_inc_ref(v_uninteresting_1381_);
lean_dec_ref(v_typeAnalysis_1379_);
v___x_1382_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1383_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
lean_inc(v_n_1368_);
v___x_1384_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1382_, v___x_1383_, v_uninteresting_1381_, v_n_1368_);
lean_dec_ref(v_uninteresting_1381_);
if (v___x_1384_ == 0)
{
uint8_t v___x_1385_; 
v___x_1385_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_1382_, v___x_1383_, v_interestingStructures_1380_, v_n_1368_);
lean_dec_ref(v_interestingStructures_1380_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_box(v___x_1385_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref(v_interestingStructures_1380_);
lean_dec(v_n_1368_);
v___x_1391_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2));
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(lean_object* v_n_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(v_n_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(lean_object* v_f_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v___x_1407_; lean_object* v_rewriteSimpCache_1408_; lean_object* v_rewriteDSimpCache_1409_; lean_object* v_acCache_1410_; lean_object* v_typeAnalysis_1411_; lean_object* v_goal_1412_; lean_object* v_hypotheses_1413_; uint8_t v_didChange_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1425_; 
v___x_1407_ = lean_st_ref_take(v_a_1405_);
v_rewriteSimpCache_1408_ = lean_ctor_get(v___x_1407_, 0);
v_rewriteDSimpCache_1409_ = lean_ctor_get(v___x_1407_, 1);
v_acCache_1410_ = lean_ctor_get(v___x_1407_, 2);
v_typeAnalysis_1411_ = lean_ctor_get(v___x_1407_, 3);
v_goal_1412_ = lean_ctor_get(v___x_1407_, 4);
v_hypotheses_1413_ = lean_ctor_get(v___x_1407_, 5);
v_didChange_1414_ = lean_ctor_get_uint8(v___x_1407_, sizeof(void*)*6);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1416_ = v___x_1407_;
v_isShared_1417_ = v_isSharedCheck_1425_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_hypotheses_1413_);
lean_inc(v_goal_1412_);
lean_inc(v_typeAnalysis_1411_);
lean_inc(v_acCache_1410_);
lean_inc(v_rewriteDSimpCache_1409_);
lean_inc(v_rewriteSimpCache_1408_);
lean_dec(v___x_1407_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1425_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = lean_apply_1(v_f_1404_, v_typeAnalysis_1411_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 3, v___x_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_rewriteSimpCache_1408_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_rewriteDSimpCache_1409_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_acCache_1410_);
lean_ctor_set(v_reuseFailAlloc_1424_, 3, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1424_, 4, v_goal_1412_);
lean_ctor_set(v_reuseFailAlloc_1424_, 5, v_hypotheses_1413_);
lean_ctor_set_uint8(v_reuseFailAlloc_1424_, sizeof(void*)*6, v_didChange_1414_);
v___x_1420_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = lean_st_ref_set(v_a_1405_, v___x_1420_);
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(lean_object* v_f_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(v_f_1426_, v_a_1427_);
lean_dec(v_a_1427_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(lean_object* v_f_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1440_; lean_object* v_rewriteSimpCache_1441_; lean_object* v_rewriteDSimpCache_1442_; lean_object* v_acCache_1443_; lean_object* v_typeAnalysis_1444_; lean_object* v_goal_1445_; lean_object* v_hypotheses_1446_; uint8_t v_didChange_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1458_; 
v___x_1440_ = lean_st_ref_take(v_a_1432_);
v_rewriteSimpCache_1441_ = lean_ctor_get(v___x_1440_, 0);
v_rewriteDSimpCache_1442_ = lean_ctor_get(v___x_1440_, 1);
v_acCache_1443_ = lean_ctor_get(v___x_1440_, 2);
v_typeAnalysis_1444_ = lean_ctor_get(v___x_1440_, 3);
v_goal_1445_ = lean_ctor_get(v___x_1440_, 4);
v_hypotheses_1446_ = lean_ctor_get(v___x_1440_, 5);
v_didChange_1447_ = lean_ctor_get_uint8(v___x_1440_, sizeof(void*)*6);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1449_ = v___x_1440_;
v_isShared_1450_ = v_isSharedCheck_1458_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_hypotheses_1446_);
lean_inc(v_goal_1445_);
lean_inc(v_typeAnalysis_1444_);
lean_inc(v_acCache_1443_);
lean_inc(v_rewriteDSimpCache_1442_);
lean_inc(v_rewriteSimpCache_1441_);
lean_dec(v___x_1440_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1458_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_apply_1(v_f_1430_, v_typeAnalysis_1444_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 3, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_rewriteSimpCache_1441_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_rewriteDSimpCache_1442_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_acCache_1443_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_goal_1445_);
lean_ctor_set(v_reuseFailAlloc_1457_, 5, v_hypotheses_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1457_, sizeof(void*)*6, v_didChange_1447_);
v___x_1453_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = lean_st_ref_set(v_a_1432_, v___x_1453_);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(lean_object* v_f_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(v_f_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(lean_object* v_n_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v___x_1473_; lean_object* v_typeAnalysis_1474_; lean_object* v_rewriteSimpCache_1475_; lean_object* v_rewriteDSimpCache_1476_; lean_object* v_acCache_1477_; lean_object* v_goal_1478_; lean_object* v_hypotheses_1479_; uint8_t v_didChange_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1504_; 
v___x_1473_ = lean_st_ref_take(v_a_1471_);
v_typeAnalysis_1474_ = lean_ctor_get(v___x_1473_, 3);
v_rewriteSimpCache_1475_ = lean_ctor_get(v___x_1473_, 0);
v_rewriteDSimpCache_1476_ = lean_ctor_get(v___x_1473_, 1);
v_acCache_1477_ = lean_ctor_get(v___x_1473_, 2);
v_goal_1478_ = lean_ctor_get(v___x_1473_, 4);
v_hypotheses_1479_ = lean_ctor_get(v___x_1473_, 5);
v_didChange_1480_ = lean_ctor_get_uint8(v___x_1473_, sizeof(void*)*6);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1482_ = v___x_1473_;
v_isShared_1483_ = v_isSharedCheck_1504_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_hypotheses_1479_);
lean_inc(v_goal_1478_);
lean_inc(v_typeAnalysis_1474_);
lean_inc(v_acCache_1477_);
lean_inc(v_rewriteDSimpCache_1476_);
lean_inc(v_rewriteSimpCache_1475_);
lean_dec(v___x_1473_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1504_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_interestingStructures_1484_; lean_object* v_interestingEnums_1485_; lean_object* v_interestingMatchers_1486_; lean_object* v_uninteresting_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1503_; 
v_interestingStructures_1484_ = lean_ctor_get(v_typeAnalysis_1474_, 0);
v_interestingEnums_1485_ = lean_ctor_get(v_typeAnalysis_1474_, 1);
v_interestingMatchers_1486_ = lean_ctor_get(v_typeAnalysis_1474_, 2);
v_uninteresting_1487_ = lean_ctor_get(v_typeAnalysis_1474_, 3);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_typeAnalysis_1474_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1489_ = v_typeAnalysis_1474_;
v_isShared_1490_ = v_isSharedCheck_1503_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_uninteresting_1487_);
lean_inc(v_interestingMatchers_1486_);
lean_inc(v_interestingEnums_1485_);
lean_inc(v_interestingStructures_1484_);
lean_dec(v_typeAnalysis_1474_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1503_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1491_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1492_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1493_ = lean_box(0);
v___x_1494_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1491_, v___x_1492_, v_interestingStructures_1484_, v_n_1470_, v___x_1493_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1494_);
v___x_1496_ = v___x_1489_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_interestingEnums_1485_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_interestingMatchers_1486_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_uninteresting_1487_);
v___x_1496_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 3, v___x_1496_);
v___x_1498_ = v___x_1482_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_rewriteSimpCache_1475_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_rewriteDSimpCache_1476_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_acCache_1477_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_goal_1478_);
lean_ctor_set(v_reuseFailAlloc_1501_, 5, v_hypotheses_1479_);
lean_ctor_set_uint8(v_reuseFailAlloc_1501_, sizeof(void*)*6, v_didChange_1480_);
v___x_1498_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_st_ref_set(v_a_1471_, v___x_1498_);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1493_);
return v___x_1500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(lean_object* v_n_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(v_n_1505_, v_a_1506_);
lean_dec(v_a_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(lean_object* v_n_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v_typeAnalysis_1520_; lean_object* v_rewriteSimpCache_1521_; lean_object* v_rewriteDSimpCache_1522_; lean_object* v_acCache_1523_; lean_object* v_goal_1524_; lean_object* v_hypotheses_1525_; uint8_t v_didChange_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1550_; 
v___x_1519_ = lean_st_ref_take(v_a_1511_);
v_typeAnalysis_1520_ = lean_ctor_get(v___x_1519_, 3);
v_rewriteSimpCache_1521_ = lean_ctor_get(v___x_1519_, 0);
v_rewriteDSimpCache_1522_ = lean_ctor_get(v___x_1519_, 1);
v_acCache_1523_ = lean_ctor_get(v___x_1519_, 2);
v_goal_1524_ = lean_ctor_get(v___x_1519_, 4);
v_hypotheses_1525_ = lean_ctor_get(v___x_1519_, 5);
v_didChange_1526_ = lean_ctor_get_uint8(v___x_1519_, sizeof(void*)*6);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1528_ = v___x_1519_;
v_isShared_1529_ = v_isSharedCheck_1550_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_hypotheses_1525_);
lean_inc(v_goal_1524_);
lean_inc(v_typeAnalysis_1520_);
lean_inc(v_acCache_1523_);
lean_inc(v_rewriteDSimpCache_1522_);
lean_inc(v_rewriteSimpCache_1521_);
lean_dec(v___x_1519_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1550_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_interestingStructures_1530_; lean_object* v_interestingEnums_1531_; lean_object* v_interestingMatchers_1532_; lean_object* v_uninteresting_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1549_; 
v_interestingStructures_1530_ = lean_ctor_get(v_typeAnalysis_1520_, 0);
v_interestingEnums_1531_ = lean_ctor_get(v_typeAnalysis_1520_, 1);
v_interestingMatchers_1532_ = lean_ctor_get(v_typeAnalysis_1520_, 2);
v_uninteresting_1533_ = lean_ctor_get(v_typeAnalysis_1520_, 3);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_typeAnalysis_1520_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1535_ = v_typeAnalysis_1520_;
v_isShared_1536_ = v_isSharedCheck_1549_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_uninteresting_1533_);
lean_inc(v_interestingMatchers_1532_);
lean_inc(v_interestingEnums_1531_);
lean_inc(v_interestingStructures_1530_);
lean_dec(v_typeAnalysis_1520_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1549_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1537_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1538_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1539_ = lean_box(0);
v___x_1540_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1537_, v___x_1538_, v_interestingStructures_1530_, v_n_1509_, v___x_1539_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1540_);
v___x_1542_ = v___x_1535_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_interestingEnums_1531_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_interestingMatchers_1532_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_uninteresting_1533_);
v___x_1542_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 3, v___x_1542_);
v___x_1544_ = v___x_1528_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_rewriteSimpCache_1521_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_rewriteDSimpCache_1522_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_acCache_1523_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_goal_1524_);
lean_ctor_set(v_reuseFailAlloc_1547_, 5, v_hypotheses_1525_);
lean_ctor_set_uint8(v_reuseFailAlloc_1547_, sizeof(void*)*6, v_didChange_1526_);
v___x_1544_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = lean_st_ref_set(v_a_1511_, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1539_);
return v___x_1546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(lean_object* v_n_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(v_n_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(lean_object* v_n_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v_typeAnalysis_1566_; lean_object* v_rewriteSimpCache_1567_; lean_object* v_rewriteDSimpCache_1568_; lean_object* v_acCache_1569_; lean_object* v_goal_1570_; lean_object* v_hypotheses_1571_; uint8_t v_didChange_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1596_; 
v___x_1565_ = lean_st_ref_take(v_a_1563_);
v_typeAnalysis_1566_ = lean_ctor_get(v___x_1565_, 3);
v_rewriteSimpCache_1567_ = lean_ctor_get(v___x_1565_, 0);
v_rewriteDSimpCache_1568_ = lean_ctor_get(v___x_1565_, 1);
v_acCache_1569_ = lean_ctor_get(v___x_1565_, 2);
v_goal_1570_ = lean_ctor_get(v___x_1565_, 4);
v_hypotheses_1571_ = lean_ctor_get(v___x_1565_, 5);
v_didChange_1572_ = lean_ctor_get_uint8(v___x_1565_, sizeof(void*)*6);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1574_ = v___x_1565_;
v_isShared_1575_ = v_isSharedCheck_1596_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_hypotheses_1571_);
lean_inc(v_goal_1570_);
lean_inc(v_typeAnalysis_1566_);
lean_inc(v_acCache_1569_);
lean_inc(v_rewriteDSimpCache_1568_);
lean_inc(v_rewriteSimpCache_1567_);
lean_dec(v___x_1565_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1596_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v_interestingStructures_1576_; lean_object* v_interestingEnums_1577_; lean_object* v_interestingMatchers_1578_; lean_object* v_uninteresting_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1595_; 
v_interestingStructures_1576_ = lean_ctor_get(v_typeAnalysis_1566_, 0);
v_interestingEnums_1577_ = lean_ctor_get(v_typeAnalysis_1566_, 1);
v_interestingMatchers_1578_ = lean_ctor_get(v_typeAnalysis_1566_, 2);
v_uninteresting_1579_ = lean_ctor_get(v_typeAnalysis_1566_, 3);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_typeAnalysis_1566_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1581_ = v_typeAnalysis_1566_;
v_isShared_1582_ = v_isSharedCheck_1595_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_uninteresting_1579_);
lean_inc(v_interestingMatchers_1578_);
lean_inc(v_interestingEnums_1577_);
lean_inc(v_interestingStructures_1576_);
lean_dec(v_typeAnalysis_1566_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1595_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1583_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1584_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1585_ = lean_box(0);
v___x_1586_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1583_, v___x_1584_, v_interestingEnums_1577_, v_n_1562_, v___x_1585_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v___x_1586_);
v___x_1588_ = v___x_1581_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_interestingStructures_1576_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_interestingMatchers_1578_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_uninteresting_1579_);
v___x_1588_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1590_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 3, v___x_1588_);
v___x_1590_ = v___x_1574_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_rewriteSimpCache_1567_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_rewriteDSimpCache_1568_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_acCache_1569_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_goal_1570_);
lean_ctor_set(v_reuseFailAlloc_1593_, 5, v_hypotheses_1571_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*6, v_didChange_1572_);
v___x_1590_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = lean_st_ref_set(v_a_1563_, v___x_1590_);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1585_);
return v___x_1592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(lean_object* v_n_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(v_n_1597_, v_a_1598_);
lean_dec(v_a_1598_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(lean_object* v_n_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v___x_1611_; lean_object* v_typeAnalysis_1612_; lean_object* v_rewriteSimpCache_1613_; lean_object* v_rewriteDSimpCache_1614_; lean_object* v_acCache_1615_; lean_object* v_goal_1616_; lean_object* v_hypotheses_1617_; uint8_t v_didChange_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1642_; 
v___x_1611_ = lean_st_ref_take(v_a_1603_);
v_typeAnalysis_1612_ = lean_ctor_get(v___x_1611_, 3);
v_rewriteSimpCache_1613_ = lean_ctor_get(v___x_1611_, 0);
v_rewriteDSimpCache_1614_ = lean_ctor_get(v___x_1611_, 1);
v_acCache_1615_ = lean_ctor_get(v___x_1611_, 2);
v_goal_1616_ = lean_ctor_get(v___x_1611_, 4);
v_hypotheses_1617_ = lean_ctor_get(v___x_1611_, 5);
v_didChange_1618_ = lean_ctor_get_uint8(v___x_1611_, sizeof(void*)*6);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1620_ = v___x_1611_;
v_isShared_1621_ = v_isSharedCheck_1642_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_hypotheses_1617_);
lean_inc(v_goal_1616_);
lean_inc(v_typeAnalysis_1612_);
lean_inc(v_acCache_1615_);
lean_inc(v_rewriteDSimpCache_1614_);
lean_inc(v_rewriteSimpCache_1613_);
lean_dec(v___x_1611_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1642_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_interestingStructures_1622_; lean_object* v_interestingEnums_1623_; lean_object* v_interestingMatchers_1624_; lean_object* v_uninteresting_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1641_; 
v_interestingStructures_1622_ = lean_ctor_get(v_typeAnalysis_1612_, 0);
v_interestingEnums_1623_ = lean_ctor_get(v_typeAnalysis_1612_, 1);
v_interestingMatchers_1624_ = lean_ctor_get(v_typeAnalysis_1612_, 2);
v_uninteresting_1625_ = lean_ctor_get(v_typeAnalysis_1612_, 3);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_typeAnalysis_1612_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1627_ = v_typeAnalysis_1612_;
v_isShared_1628_ = v_isSharedCheck_1641_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_uninteresting_1625_);
lean_inc(v_interestingMatchers_1624_);
lean_inc(v_interestingEnums_1623_);
lean_inc(v_interestingStructures_1622_);
lean_dec(v_typeAnalysis_1612_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1641_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1629_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1630_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1631_ = lean_box(0);
v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1629_, v___x_1630_, v_interestingEnums_1623_, v_n_1601_, v___x_1631_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v___x_1632_);
v___x_1634_ = v___x_1627_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_interestingStructures_1622_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_interestingMatchers_1624_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_uninteresting_1625_);
v___x_1634_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1636_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 3, v___x_1634_);
v___x_1636_ = v___x_1620_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_rewriteSimpCache_1613_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_rewriteDSimpCache_1614_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_acCache_1615_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v_goal_1616_);
lean_ctor_set(v_reuseFailAlloc_1639_, 5, v_hypotheses_1617_);
lean_ctor_set_uint8(v_reuseFailAlloc_1639_, sizeof(void*)*6, v_didChange_1618_);
v___x_1636_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_st_ref_set(v_a_1603_, v___x_1636_);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1631_);
return v___x_1638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(lean_object* v_n_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(v_n_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(lean_object* v_n_1654_, lean_object* v_k_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v___x_1658_; lean_object* v_typeAnalysis_1659_; lean_object* v_rewriteSimpCache_1660_; lean_object* v_rewriteDSimpCache_1661_; lean_object* v_acCache_1662_; lean_object* v_goal_1663_; lean_object* v_hypotheses_1664_; uint8_t v_didChange_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1689_; 
v___x_1658_ = lean_st_ref_take(v_a_1656_);
v_typeAnalysis_1659_ = lean_ctor_get(v___x_1658_, 3);
v_rewriteSimpCache_1660_ = lean_ctor_get(v___x_1658_, 0);
v_rewriteDSimpCache_1661_ = lean_ctor_get(v___x_1658_, 1);
v_acCache_1662_ = lean_ctor_get(v___x_1658_, 2);
v_goal_1663_ = lean_ctor_get(v___x_1658_, 4);
v_hypotheses_1664_ = lean_ctor_get(v___x_1658_, 5);
v_didChange_1665_ = lean_ctor_get_uint8(v___x_1658_, sizeof(void*)*6);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1667_ = v___x_1658_;
v_isShared_1668_ = v_isSharedCheck_1689_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_hypotheses_1664_);
lean_inc(v_goal_1663_);
lean_inc(v_typeAnalysis_1659_);
lean_inc(v_acCache_1662_);
lean_inc(v_rewriteDSimpCache_1661_);
lean_inc(v_rewriteSimpCache_1660_);
lean_dec(v___x_1658_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1689_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_interestingStructures_1669_; lean_object* v_interestingEnums_1670_; lean_object* v_interestingMatchers_1671_; lean_object* v_uninteresting_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1688_; 
v_interestingStructures_1669_ = lean_ctor_get(v_typeAnalysis_1659_, 0);
v_interestingEnums_1670_ = lean_ctor_get(v_typeAnalysis_1659_, 1);
v_interestingMatchers_1671_ = lean_ctor_get(v_typeAnalysis_1659_, 2);
v_uninteresting_1672_ = lean_ctor_get(v_typeAnalysis_1659_, 3);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_typeAnalysis_1659_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1674_ = v_typeAnalysis_1659_;
v_isShared_1675_ = v_isSharedCheck_1688_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_uninteresting_1672_);
lean_inc(v_interestingMatchers_1671_);
lean_inc(v_interestingEnums_1670_);
lean_inc(v_interestingStructures_1669_);
lean_dec(v_typeAnalysis_1659_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1688_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1676_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1677_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1678_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1676_, v___x_1677_, v_interestingMatchers_1671_, v_n_1654_, v_k_1655_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 2, v___x_1678_);
v___x_1680_ = v___x_1674_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_interestingStructures_1669_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_interestingEnums_1670_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_uninteresting_1672_);
v___x_1680_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1682_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 3, v___x_1680_);
v___x_1682_ = v___x_1667_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_rewriteSimpCache_1660_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_rewriteDSimpCache_1661_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_acCache_1662_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_goal_1663_);
lean_ctor_set(v_reuseFailAlloc_1686_, 5, v_hypotheses_1664_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*6, v_didChange_1665_);
v___x_1682_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = lean_st_ref_set(v_a_1656_, v___x_1682_);
v___x_1684_ = lean_box(0);
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
return v___x_1685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(lean_object* v_n_1690_, lean_object* v_k_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(v_n_1690_, v_k_1691_, v_a_1692_);
lean_dec(v_a_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(lean_object* v_n_1695_, lean_object* v_k_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v___x_1706_; lean_object* v_typeAnalysis_1707_; lean_object* v_rewriteSimpCache_1708_; lean_object* v_rewriteDSimpCache_1709_; lean_object* v_acCache_1710_; lean_object* v_goal_1711_; lean_object* v_hypotheses_1712_; uint8_t v_didChange_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1737_; 
v___x_1706_ = lean_st_ref_take(v_a_1698_);
v_typeAnalysis_1707_ = lean_ctor_get(v___x_1706_, 3);
v_rewriteSimpCache_1708_ = lean_ctor_get(v___x_1706_, 0);
v_rewriteDSimpCache_1709_ = lean_ctor_get(v___x_1706_, 1);
v_acCache_1710_ = lean_ctor_get(v___x_1706_, 2);
v_goal_1711_ = lean_ctor_get(v___x_1706_, 4);
v_hypotheses_1712_ = lean_ctor_get(v___x_1706_, 5);
v_didChange_1713_ = lean_ctor_get_uint8(v___x_1706_, sizeof(void*)*6);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1715_ = v___x_1706_;
v_isShared_1716_ = v_isSharedCheck_1737_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_hypotheses_1712_);
lean_inc(v_goal_1711_);
lean_inc(v_typeAnalysis_1707_);
lean_inc(v_acCache_1710_);
lean_inc(v_rewriteDSimpCache_1709_);
lean_inc(v_rewriteSimpCache_1708_);
lean_dec(v___x_1706_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1737_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v_interestingStructures_1717_; lean_object* v_interestingEnums_1718_; lean_object* v_interestingMatchers_1719_; lean_object* v_uninteresting_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1736_; 
v_interestingStructures_1717_ = lean_ctor_get(v_typeAnalysis_1707_, 0);
v_interestingEnums_1718_ = lean_ctor_get(v_typeAnalysis_1707_, 1);
v_interestingMatchers_1719_ = lean_ctor_get(v_typeAnalysis_1707_, 2);
v_uninteresting_1720_ = lean_ctor_get(v_typeAnalysis_1707_, 3);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_typeAnalysis_1707_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1722_ = v_typeAnalysis_1707_;
v_isShared_1723_ = v_isSharedCheck_1736_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_uninteresting_1720_);
lean_inc(v_interestingMatchers_1719_);
lean_inc(v_interestingEnums_1718_);
lean_inc(v_interestingStructures_1717_);
lean_dec(v_typeAnalysis_1707_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1736_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1724_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1725_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1726_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_1724_, v___x_1725_, v_interestingMatchers_1719_, v_n_1695_, v_k_1696_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 2, v___x_1726_);
v___x_1728_ = v___x_1722_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_interestingStructures_1717_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_interestingEnums_1718_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_uninteresting_1720_);
v___x_1728_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1730_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 3, v___x_1728_);
v___x_1730_ = v___x_1715_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_rewriteSimpCache_1708_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_rewriteDSimpCache_1709_);
lean_ctor_set(v_reuseFailAlloc_1734_, 2, v_acCache_1710_);
lean_ctor_set(v_reuseFailAlloc_1734_, 3, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1734_, 4, v_goal_1711_);
lean_ctor_set(v_reuseFailAlloc_1734_, 5, v_hypotheses_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1734_, sizeof(void*)*6, v_didChange_1713_);
v___x_1730_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1731_ = lean_st_ref_set(v_a_1698_, v___x_1730_);
v___x_1732_ = lean_box(0);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
return v___x_1733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(lean_object* v_n_1738_, lean_object* v_k_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(v_n_1738_, v_k_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(lean_object* v_n_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; lean_object* v_typeAnalysis_1754_; lean_object* v_rewriteSimpCache_1755_; lean_object* v_rewriteDSimpCache_1756_; lean_object* v_acCache_1757_; lean_object* v_goal_1758_; lean_object* v_hypotheses_1759_; uint8_t v_didChange_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1784_; 
v___x_1753_ = lean_st_ref_take(v_a_1751_);
v_typeAnalysis_1754_ = lean_ctor_get(v___x_1753_, 3);
v_rewriteSimpCache_1755_ = lean_ctor_get(v___x_1753_, 0);
v_rewriteDSimpCache_1756_ = lean_ctor_get(v___x_1753_, 1);
v_acCache_1757_ = lean_ctor_get(v___x_1753_, 2);
v_goal_1758_ = lean_ctor_get(v___x_1753_, 4);
v_hypotheses_1759_ = lean_ctor_get(v___x_1753_, 5);
v_didChange_1760_ = lean_ctor_get_uint8(v___x_1753_, sizeof(void*)*6);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1762_ = v___x_1753_;
v_isShared_1763_ = v_isSharedCheck_1784_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_hypotheses_1759_);
lean_inc(v_goal_1758_);
lean_inc(v_typeAnalysis_1754_);
lean_inc(v_acCache_1757_);
lean_inc(v_rewriteDSimpCache_1756_);
lean_inc(v_rewriteSimpCache_1755_);
lean_dec(v___x_1753_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1784_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v_interestingStructures_1764_; lean_object* v_interestingEnums_1765_; lean_object* v_interestingMatchers_1766_; lean_object* v_uninteresting_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1783_; 
v_interestingStructures_1764_ = lean_ctor_get(v_typeAnalysis_1754_, 0);
v_interestingEnums_1765_ = lean_ctor_get(v_typeAnalysis_1754_, 1);
v_interestingMatchers_1766_ = lean_ctor_get(v_typeAnalysis_1754_, 2);
v_uninteresting_1767_ = lean_ctor_get(v_typeAnalysis_1754_, 3);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_typeAnalysis_1754_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1769_ = v_typeAnalysis_1754_;
v_isShared_1770_ = v_isSharedCheck_1783_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_uninteresting_1767_);
lean_inc(v_interestingMatchers_1766_);
lean_inc(v_interestingEnums_1765_);
lean_inc(v_interestingStructures_1764_);
lean_dec(v_typeAnalysis_1754_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1783_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1771_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1772_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1773_ = lean_box(0);
v___x_1774_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1771_, v___x_1772_, v_uninteresting_1767_, v_n_1750_, v___x_1773_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 3, v___x_1774_);
v___x_1776_ = v___x_1769_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_interestingStructures_1764_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_interestingEnums_1765_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_interestingMatchers_1766_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1778_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 3, v___x_1776_);
v___x_1778_ = v___x_1762_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_rewriteSimpCache_1755_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_rewriteDSimpCache_1756_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v_acCache_1757_);
lean_ctor_set(v_reuseFailAlloc_1781_, 3, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1781_, 4, v_goal_1758_);
lean_ctor_set(v_reuseFailAlloc_1781_, 5, v_hypotheses_1759_);
lean_ctor_set_uint8(v_reuseFailAlloc_1781_, sizeof(void*)*6, v_didChange_1760_);
v___x_1778_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = lean_st_ref_set(v_a_1751_, v___x_1778_);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1773_);
return v___x_1780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(lean_object* v_n_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(v_n_1785_, v_a_1786_);
lean_dec(v_a_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(lean_object* v_n_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v_typeAnalysis_1800_; lean_object* v_rewriteSimpCache_1801_; lean_object* v_rewriteDSimpCache_1802_; lean_object* v_acCache_1803_; lean_object* v_goal_1804_; lean_object* v_hypotheses_1805_; uint8_t v_didChange_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1830_; 
v___x_1799_ = lean_st_ref_take(v_a_1791_);
v_typeAnalysis_1800_ = lean_ctor_get(v___x_1799_, 3);
v_rewriteSimpCache_1801_ = lean_ctor_get(v___x_1799_, 0);
v_rewriteDSimpCache_1802_ = lean_ctor_get(v___x_1799_, 1);
v_acCache_1803_ = lean_ctor_get(v___x_1799_, 2);
v_goal_1804_ = lean_ctor_get(v___x_1799_, 4);
v_hypotheses_1805_ = lean_ctor_get(v___x_1799_, 5);
v_didChange_1806_ = lean_ctor_get_uint8(v___x_1799_, sizeof(void*)*6);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1808_ = v___x_1799_;
v_isShared_1809_ = v_isSharedCheck_1830_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_hypotheses_1805_);
lean_inc(v_goal_1804_);
lean_inc(v_typeAnalysis_1800_);
lean_inc(v_acCache_1803_);
lean_inc(v_rewriteDSimpCache_1802_);
lean_inc(v_rewriteSimpCache_1801_);
lean_dec(v___x_1799_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1830_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v_interestingStructures_1810_; lean_object* v_interestingEnums_1811_; lean_object* v_interestingMatchers_1812_; lean_object* v_uninteresting_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1829_; 
v_interestingStructures_1810_ = lean_ctor_get(v_typeAnalysis_1800_, 0);
v_interestingEnums_1811_ = lean_ctor_get(v_typeAnalysis_1800_, 1);
v_interestingMatchers_1812_ = lean_ctor_get(v_typeAnalysis_1800_, 2);
v_uninteresting_1813_ = lean_ctor_get(v_typeAnalysis_1800_, 3);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_typeAnalysis_1800_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1815_ = v_typeAnalysis_1800_;
v_isShared_1816_ = v_isSharedCheck_1829_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_uninteresting_1813_);
lean_inc(v_interestingMatchers_1812_);
lean_inc(v_interestingEnums_1811_);
lean_inc(v_interestingStructures_1810_);
lean_dec(v_typeAnalysis_1800_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1829_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1817_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0));
v___x_1818_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1));
v___x_1819_ = lean_box(0);
v___x_1820_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_1817_, v___x_1818_, v_uninteresting_1813_, v_n_1789_, v___x_1819_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 3, v___x_1820_);
v___x_1822_ = v___x_1815_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_interestingStructures_1810_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_interestingEnums_1811_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_interestingMatchers_1812_);
lean_ctor_set(v_reuseFailAlloc_1828_, 3, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 3, v___x_1822_);
v___x_1824_ = v___x_1808_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_rewriteSimpCache_1801_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_rewriteDSimpCache_1802_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_acCache_1803_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v___x_1822_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_goal_1804_);
lean_ctor_set(v_reuseFailAlloc_1827_, 5, v_hypotheses_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*6, v_didChange_1806_);
v___x_1824_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_st_ref_set(v_a_1791_, v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1819_);
return v___x_1826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(lean_object* v_n_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(v_n_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
return v_res_1841_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = lean_box(0);
v___x_1843_ = lean_unsigned_to_nat(16u);
v___x_1844_ = lean_mk_array(v___x_1843_, v___x_1842_);
return v___x_1844_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0);
v___x_1846_ = lean_unsigned_to_nat(0u);
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
lean_ctor_set(v___x_1847_, 1, v___x_1845_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
v___x_1849_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
lean_ctor_set(v___x_1849_, 2, v___x_1848_);
lean_ctor_set(v___x_1849_, 3, v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(lean_object* v_cfg_1852_, lean_object* v_goal_1853_, lean_object* v_x_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1862_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_1863_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_1864_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_1865_ = 0;
v___x_1866_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1866_, 0, v___x_1862_);
lean_ctor_set(v___x_1866_, 1, v___x_1862_);
lean_ctor_set(v___x_1866_, 2, v___x_1862_);
lean_ctor_set(v___x_1866_, 3, v___x_1863_);
lean_ctor_set(v___x_1866_, 4, v_goal_1853_);
lean_ctor_set(v___x_1866_, 5, v___x_1864_);
lean_ctor_set_uint8(v___x_1866_, sizeof(void*)*6, v___x_1865_);
v___x_1867_ = lean_st_mk_ref(v___x_1866_);
lean_inc(v_a_1860_);
lean_inc_ref(v_a_1859_);
lean_inc(v_a_1858_);
lean_inc_ref(v_a_1857_);
lean_inc(v_a_1856_);
lean_inc_ref(v_a_1855_);
lean_inc(v___x_1867_);
v___x_1868_ = lean_apply_9(v_x_1854_, v_cfg_1852_, v___x_1867_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, lean_box(0));
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1878_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1878_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1878_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1873_ = lean_st_ref_get(v___x_1867_);
lean_dec(v___x_1867_);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v_a_1869_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1874_);
v___x_1876_ = v___x_1871_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v___x_1867_);
v_a_1879_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1868_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1868_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(lean_object* v_cfg_1887_, lean_object* v_goal_1888_, lean_object* v_x_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(v_cfg_1887_, v_goal_1888_, v_x_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(lean_object* v_00_u03b1_1898_, lean_object* v_cfg_1899_, lean_object* v_goal_1900_, lean_object* v_x_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1909_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_1910_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_1911_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_1912_ = 0;
v___x_1913_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1913_, 0, v___x_1909_);
lean_ctor_set(v___x_1913_, 1, v___x_1909_);
lean_ctor_set(v___x_1913_, 2, v___x_1909_);
lean_ctor_set(v___x_1913_, 3, v___x_1910_);
lean_ctor_set(v___x_1913_, 4, v_goal_1900_);
lean_ctor_set(v___x_1913_, 5, v___x_1911_);
lean_ctor_set_uint8(v___x_1913_, sizeof(void*)*6, v___x_1912_);
v___x_1914_ = lean_st_mk_ref(v___x_1913_);
lean_inc(v_a_1907_);
lean_inc_ref(v_a_1906_);
lean_inc(v_a_1905_);
lean_inc_ref(v_a_1904_);
lean_inc(v_a_1903_);
lean_inc_ref(v_a_1902_);
lean_inc(v___x_1914_);
v___x_1915_ = lean_apply_9(v_x_1901_, v_cfg_1899_, v___x_1914_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, lean_box(0));
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1925_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1925_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1925_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1920_ = lean_st_ref_get(v___x_1914_);
lean_dec(v___x_1914_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_a_1916_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1921_);
v___x_1923_ = v___x_1918_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec(v___x_1914_);
v_a_1926_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1915_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1915_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(lean_object* v_00_u03b1_1934_, lean_object* v_cfg_1935_, lean_object* v_goal_1936_, lean_object* v_x_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(v_00_u03b1_1934_, v_cfg_1935_, v_goal_1936_, v_x_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(lean_object* v_cfg_1946_, lean_object* v_goal_1947_, lean_object* v_x_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1956_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_1957_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_1958_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_1959_ = 0;
v___x_1960_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1960_, 0, v___x_1956_);
lean_ctor_set(v___x_1960_, 1, v___x_1956_);
lean_ctor_set(v___x_1960_, 2, v___x_1956_);
lean_ctor_set(v___x_1960_, 3, v___x_1957_);
lean_ctor_set(v___x_1960_, 4, v_goal_1947_);
lean_ctor_set(v___x_1960_, 5, v___x_1958_);
lean_ctor_set_uint8(v___x_1960_, sizeof(void*)*6, v___x_1959_);
v___x_1961_ = lean_st_mk_ref(v___x_1960_);
lean_inc(v_a_1954_);
lean_inc_ref(v_a_1953_);
lean_inc(v_a_1952_);
lean_inc_ref(v_a_1951_);
lean_inc(v_a_1950_);
lean_inc_ref(v_a_1949_);
lean_inc(v___x_1961_);
v___x_1962_ = lean_apply_9(v_x_1948_, v_cfg_1946_, v___x_1961_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, lean_box(0));
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1971_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = lean_st_ref_get(v___x_1961_);
lean_dec(v___x_1961_);
lean_dec(v___x_1967_);
if (v_isShared_1966_ == 0)
{
v___x_1969_ = v___x_1965_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1963_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
else
{
lean_dec(v___x_1961_);
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg___boxed(lean_object* v_cfg_1972_, lean_object* v_goal_1973_, lean_object* v_x_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___redArg(v_cfg_1972_, v_goal_1973_, v_x_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(lean_object* v_00_u03b1_1983_, lean_object* v_cfg_1984_, lean_object* v_goal_1985_, lean_object* v_x_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1994_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_1995_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2);
v___x_1996_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
v___x_1997_ = 0;
v___x_1998_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_1998_, 0, v___x_1994_);
lean_ctor_set(v___x_1998_, 1, v___x_1994_);
lean_ctor_set(v___x_1998_, 2, v___x_1994_);
lean_ctor_set(v___x_1998_, 3, v___x_1995_);
lean_ctor_set(v___x_1998_, 4, v_goal_1985_);
lean_ctor_set(v___x_1998_, 5, v___x_1996_);
lean_ctor_set_uint8(v___x_1998_, sizeof(void*)*6, v___x_1997_);
v___x_1999_ = lean_st_mk_ref(v___x_1998_);
lean_inc(v_a_1992_);
lean_inc_ref(v_a_1991_);
lean_inc(v_a_1990_);
lean_inc_ref(v_a_1989_);
lean_inc(v_a_1988_);
lean_inc_ref(v_a_1987_);
lean_inc(v___x_1999_);
v___x_2000_ = lean_apply_9(v_x_1986_, v_cfg_1984_, v___x_1999_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, lean_box(0));
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2009_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_st_ref_get(v___x_1999_);
lean_dec(v___x_1999_);
lean_dec(v___x_2005_);
if (v_isShared_2004_ == 0)
{
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2001_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
else
{
lean_dec(v___x_1999_);
return v___x_2000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27___boxed(lean_object* v_00_u03b1_2010_, lean_object* v_cfg_2011_, lean_object* v_goal_2012_, lean_object* v_x_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run_x27(v_00_u03b1_2010_, v_cfg_2011_, v_goal_2012_, v_x_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___lam__0(lean_object* v_x_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___x_2032_; 
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
v___x_2032_ = lean_apply_9(v_x_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, lean_box(0));
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___lam__0___boxed(lean_object* v_x_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___lam__0(v_x_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg(lean_object* v_mvarId_2044_, lean_object* v_x_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___f_2055_; lean_object* v___x_2056_; 
lean_inc(v___y_2049_);
lean_inc_ref(v___y_2048_);
lean_inc(v___y_2047_);
lean_inc_ref(v___y_2046_);
v___f_2055_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_2055_, 0, v_x_2045_);
lean_closure_set(v___f_2055_, 1, v___y_2046_);
lean_closure_set(v___f_2055_, 2, v___y_2047_);
lean_closure_set(v___f_2055_, 3, v___y_2048_);
lean_closure_set(v___f_2055_, 4, v___y_2049_);
v___x_2056_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2044_, v___f_2055_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
if (lean_obj_tag(v___x_2056_) == 0)
{
return v___x_2056_;
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg___boxed(lean_object* v_mvarId_2065_, lean_object* v_x_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg(v_mvarId_2065_, v_x_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1(lean_object* v_00_u03b1_2077_, lean_object* v_mvarId_2078_, lean_object* v_x_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg(v_mvarId_2078_, v_x_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___boxed(lean_object* v_00_u03b1_2090_, lean_object* v_mvarId_2091_, lean_object* v_x_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1(v_00_u03b1_2090_, v_mvarId_2091_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg(size_t v_sz_2103_, size_t v_i_2104_, lean_object* v_bs_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
uint8_t v___x_2113_; 
v___x_2113_ = lean_usize_dec_lt(v_i_2104_, v_sz_2103_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_bs_2105_);
return v___x_2114_;
}
else
{
lean_object* v_v_2115_; lean_object* v___x_2116_; 
v_v_2115_ = lean_array_uget(v_bs_2105_, v_i_2104_);
lean_inc(v_v_2115_);
v___x_2116_ = l_Lean_FVarId_getUserName___redArg(v_v_2115_, v___y_2108_, v___y_2110_, v___y_2111_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
lean_inc(v_v_2115_);
v___x_2118_ = l_Lean_FVarId_getType___redArg(v_v_2115_, v___y_2108_, v___y_2110_, v___y_2111_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2120_ = l_Lean_Meta_Sym_instantiateMVarsS(v_a_2119_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; lean_object* v_bs_x27_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; size_t v___x_2127_; size_t v___x_2128_; lean_object* v___x_2129_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2120_, 1);
v___x_2122_ = lean_unsigned_to_nat(0u);
v_bs_x27_2123_ = lean_array_uset(v_bs_2105_, v_i_2104_, v___x_2122_);
lean_inc(v_v_2115_);
v___x_2124_ = l_Lean_mkFVar(v_v_2115_);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v_v_2115_);
v___x_2126_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2126_, 0, v_a_2117_);
lean_ctor_set(v___x_2126_, 1, v_a_2121_);
lean_ctor_set(v___x_2126_, 2, v___x_2124_);
lean_ctor_set(v___x_2126_, 3, v___x_2125_);
v___x_2127_ = ((size_t)1ULL);
v___x_2128_ = lean_usize_add(v_i_2104_, v___x_2127_);
v___x_2129_ = lean_array_uset(v_bs_x27_2123_, v_i_2104_, v___x_2126_);
v_i_2104_ = v___x_2128_;
v_bs_2105_ = v___x_2129_;
goto _start;
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec(v_a_2117_);
lean_dec(v_v_2115_);
lean_dec_ref(v_bs_2105_);
v_a_2131_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2120_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2120_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec(v_a_2117_);
lean_dec(v_v_2115_);
lean_dec_ref(v_bs_2105_);
v_a_2139_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2118_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2118_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec(v_v_2115_);
lean_dec_ref(v_bs_2105_);
v_a_2147_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2116_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2116_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg___boxed(lean_object* v_sz_2155_, lean_object* v_i_2156_, lean_object* v_bs_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
size_t v_sz_boxed_2165_; size_t v_i_boxed_2166_; lean_object* v_res_2167_; 
v_sz_boxed_2165_ = lean_unbox_usize(v_sz_2155_);
lean_dec(v_sz_2155_);
v_i_boxed_2166_ = lean_unbox_usize(v_i_2156_);
lean_dec(v_i_2156_);
v_res_2167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg(v_sz_boxed_2165_, v_i_boxed_2166_, v_bs_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___lam__0(lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_Meta_getPropHyps(v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; size_t v_sz_2179_; size_t v___x_2180_; lean_object* v___x_2181_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v_sz_2179_ = lean_array_size(v_a_2178_);
v___x_2180_ = ((size_t)0ULL);
v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg(v_sz_2179_, v___x_2180_, v_a_2178_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2206_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2206_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2206_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; lean_object* v_rewriteSimpCache_2187_; lean_object* v_rewriteDSimpCache_2188_; lean_object* v_acCache_2189_; lean_object* v_typeAnalysis_2190_; lean_object* v_goal_2191_; uint8_t v_didChange_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2204_; 
v___x_2186_ = lean_st_ref_take(v___y_2169_);
v_rewriteSimpCache_2187_ = lean_ctor_get(v___x_2186_, 0);
v_rewriteDSimpCache_2188_ = lean_ctor_get(v___x_2186_, 1);
v_acCache_2189_ = lean_ctor_get(v___x_2186_, 2);
v_typeAnalysis_2190_ = lean_ctor_get(v___x_2186_, 3);
v_goal_2191_ = lean_ctor_get(v___x_2186_, 4);
v_didChange_2192_ = lean_ctor_get_uint8(v___x_2186_, sizeof(void*)*6);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; 
v_unused_2205_ = lean_ctor_get(v___x_2186_, 5);
lean_dec(v_unused_2205_);
v___x_2194_ = v___x_2186_;
v_isShared_2195_ = v_isSharedCheck_2204_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_goal_2191_);
lean_inc(v_typeAnalysis_2190_);
lean_inc(v_acCache_2189_);
lean_inc(v_rewriteDSimpCache_2188_);
lean_inc(v_rewriteSimpCache_2187_);
lean_dec(v___x_2186_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2204_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 5, v_a_2182_);
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_rewriteSimpCache_2187_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_rewriteDSimpCache_2188_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_acCache_2189_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_typeAnalysis_2190_);
lean_ctor_set(v_reuseFailAlloc_2203_, 4, v_goal_2191_);
lean_ctor_set(v_reuseFailAlloc_2203_, 5, v_a_2182_);
lean_ctor_set_uint8(v_reuseFailAlloc_2203_, sizeof(void*)*6, v_didChange_2192_);
v___x_2197_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2198_ = lean_st_ref_set(v___y_2169_, v___x_2197_);
v___x_2199_ = lean_box(0);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2199_);
v___x_2201_ = v___x_2184_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
v_a_2207_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2181_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2181_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
v_a_2215_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2177_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2177_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___lam__0___boxed(lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___lam__0(v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal(lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v___x_2243_; lean_object* v_rewriteSimpCache_2244_; lean_object* v_rewriteDSimpCache_2245_; lean_object* v_acCache_2246_; lean_object* v_typeAnalysis_2247_; lean_object* v_goal_2248_; lean_object* v_hypotheses_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2262_; 
v___x_2243_ = lean_st_ref_take(v_a_2235_);
v_rewriteSimpCache_2244_ = lean_ctor_get(v___x_2243_, 0);
v_rewriteDSimpCache_2245_ = lean_ctor_get(v___x_2243_, 1);
v_acCache_2246_ = lean_ctor_get(v___x_2243_, 2);
v_typeAnalysis_2247_ = lean_ctor_get(v___x_2243_, 3);
v_goal_2248_ = lean_ctor_get(v___x_2243_, 4);
v_hypotheses_2249_ = lean_ctor_get(v___x_2243_, 5);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2251_ = v___x_2243_;
v_isShared_2252_ = v_isSharedCheck_2262_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_hypotheses_2249_);
lean_inc(v_goal_2248_);
lean_inc(v_typeAnalysis_2247_);
lean_inc(v_acCache_2246_);
lean_inc(v_rewriteDSimpCache_2245_);
lean_inc(v_rewriteSimpCache_2244_);
lean_dec(v___x_2243_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2262_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
uint8_t v___x_2253_; lean_object* v___x_2255_; 
v___x_2253_ = 1;
if (v_isShared_2252_ == 0)
{
v___x_2255_ = v___x_2251_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_rewriteSimpCache_2244_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_rewriteDSimpCache_2245_);
lean_ctor_set(v_reuseFailAlloc_2261_, 2, v_acCache_2246_);
lean_ctor_set(v_reuseFailAlloc_2261_, 3, v_typeAnalysis_2247_);
lean_ctor_set(v_reuseFailAlloc_2261_, 4, v_goal_2248_);
lean_ctor_set(v_reuseFailAlloc_2261_, 5, v_hypotheses_2249_);
v___x_2255_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v_goal_2258_; lean_object* v___f_2259_; lean_object* v___x_2260_; 
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*6, v___x_2253_);
v___x_2256_ = lean_st_ref_set(v_a_2235_, v___x_2255_);
v___x_2257_ = lean_st_ref_get(v_a_2235_);
v_goal_2258_ = lean_ctor_get(v___x_2257_, 4);
lean_inc(v_goal_2258_);
lean_dec(v___x_2257_);
v___f_2259_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___closed__0));
v___x_2260_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__1___redArg(v_goal_2258_, v___f_2259_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
return v___x_2260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal___boxed(lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal(v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0(size_t v_sz_2273_, size_t v_i_2274_, lean_object* v_bs_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___redArg(v_sz_2273_, v_i_2274_, v_bs_2275_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0___boxed(lean_object* v_sz_2286_, lean_object* v_i_2287_, lean_object* v_bs_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
size_t v_sz_boxed_2298_; size_t v_i_boxed_2299_; lean_object* v_res_2300_; 
v_sz_boxed_2298_ = lean_unbox_usize(v_sz_2286_);
lean_dec(v_sz_2286_);
v_i_boxed_2299_ = lean_unbox_usize(v_i_2287_);
lean_dec(v_i_2287_);
v_res_2300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_collectHypsFromGoal_spec__0(v_sz_boxed_2298_, v_i_boxed_2299_, v_bs_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
return v_res_2300_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0(void){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_instMonadEIO(lean_box(0));
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__0);
v___x_2303_ = l_StateRefT_x27_instMonad___redArg(v___x_2302_);
return v___x_2303_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2311_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2312_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2311_, v___x_2310_);
return v___x_2312_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___f_2314_; lean_object* v___x_2315_; 
v___x_2313_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__8);
v___f_2314_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2315_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2314_, v___x_2313_);
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__9);
v___x_2317_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2318_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2317_, v___x_2316_);
return v___x_2318_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___f_2320_; lean_object* v___x_2321_; 
v___x_2319_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__10);
v___f_2320_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2321_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2320_, v___x_2319_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__11);
v___x_2323_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2324_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2323_, v___x_2322_);
return v___x_2324_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___f_2326_; lean_object* v___x_2327_; 
v___x_2325_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__12);
v___f_2326_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2327_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2326_, v___x_2325_);
return v___x_2327_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20(void){
_start:
{
lean_object* v_cls_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v_cls_2338_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_2339_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_2340_ = l_Lean_Name_append(v___x_2339_, v_cls_2338_);
return v___x_2340_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2343_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2344_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2345_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22));
v___x_2346_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2345_, v___x_2344_, v___x_2343_);
return v___x_2346_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___f_2348_; lean_object* v___f_2349_; lean_object* v___x_2350_; 
v___x_2347_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__23);
v___f_2348_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2349_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21));
v___x_2350_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2349_, v___f_2348_, v___x_2347_);
return v___x_2350_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2351_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__24);
v___x_2352_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2353_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22));
v___x_2354_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2353_, v___x_2352_, v___x_2351_);
return v___x_2354_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___f_2356_; lean_object* v___f_2357_; lean_object* v___x_2358_; 
v___x_2355_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__25);
v___f_2356_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2357_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21));
v___x_2358_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2357_, v___f_2356_, v___x_2355_);
return v___x_2358_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2359_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__26);
v___x_2360_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2361_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22));
v___x_2362_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2361_, v___x_2360_, v___x_2359_);
return v___x_2362_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___f_2364_; lean_object* v___f_2365_; lean_object* v___x_2366_; 
v___x_2363_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__27);
v___f_2364_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2365_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21));
v___x_2366_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2365_, v___f_2364_, v___x_2363_);
return v___x_2366_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___f_2369_; 
v___x_2367_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2368_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2369_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2369_, 0, v___x_2368_);
lean_closure_set(v___f_2369_, 1, v___x_2367_);
return v___f_2369_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30(void){
_start:
{
lean_object* v___f_2370_; lean_object* v___f_2371_; lean_object* v___f_2372_; 
v___f_2370_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2371_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__29);
v___f_2372_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2372_, 0, v___f_2371_);
lean_closure_set(v___f_2372_, 1, v___f_2370_);
return v___f_2372_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___f_2374_; lean_object* v___f_2375_; 
v___x_2373_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___f_2374_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__30);
v___f_2375_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2375_, 0, v___f_2374_);
lean_closure_set(v___f_2375_, 1, v___x_2373_);
return v___f_2375_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32(void){
_start:
{
lean_object* v___f_2376_; lean_object* v___f_2377_; lean_object* v___f_2378_; 
v___f_2376_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___f_2377_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__31);
v___f_2378_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2378_, 0, v___f_2377_);
lean_closure_set(v___f_2378_, 1, v___f_2376_);
return v___f_2378_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__33));
v___x_2381_ = l_Lean_stringToMessageData(v___x_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(lean_object* v_hyp_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v___y_2393_; lean_object* v___x_2413_; lean_object* v_toApplicative_2414_; lean_object* v_toFunctor_2415_; lean_object* v_toSeq_2416_; lean_object* v_toSeqLeft_2417_; lean_object* v_toSeqRight_2418_; lean_object* v___f_2419_; lean_object* v___f_2420_; lean_object* v___f_2421_; lean_object* v___f_2422_; lean_object* v___x_2423_; lean_object* v___f_2424_; lean_object* v___f_2425_; lean_object* v___f_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v_toApplicative_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2477_; 
v___x_2413_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1);
v_toApplicative_2414_ = lean_ctor_get(v___x_2413_, 0);
v_toFunctor_2415_ = lean_ctor_get(v_toApplicative_2414_, 0);
v_toSeq_2416_ = lean_ctor_get(v_toApplicative_2414_, 2);
v_toSeqLeft_2417_ = lean_ctor_get(v_toApplicative_2414_, 3);
v_toSeqRight_2418_ = lean_ctor_get(v_toApplicative_2414_, 4);
v___f_2419_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2));
v___f_2420_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3));
lean_inc_ref_n(v_toFunctor_2415_, 2);
v___f_2421_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2421_, 0, v_toFunctor_2415_);
v___f_2422_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2422_, 0, v_toFunctor_2415_);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___f_2421_);
lean_ctor_set(v___x_2423_, 1, v___f_2422_);
lean_inc(v_toSeqRight_2418_);
v___f_2424_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2424_, 0, v_toSeqRight_2418_);
lean_inc(v_toSeqLeft_2417_);
v___f_2425_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2425_, 0, v_toSeqLeft_2417_);
lean_inc(v_toSeq_2416_);
v___f_2426_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2426_, 0, v_toSeq_2416_);
v___x_2427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2423_);
lean_ctor_set(v___x_2427_, 1, v___f_2419_);
lean_ctor_set(v___x_2427_, 2, v___f_2426_);
lean_ctor_set(v___x_2427_, 3, v___f_2425_);
lean_ctor_set(v___x_2427_, 4, v___f_2424_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v___f_2420_);
v___x_2429_ = l_StateRefT_x27_instMonad___redArg(v___x_2428_);
v_toApplicative_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v___x_2429_, 1);
lean_dec(v_unused_2478_);
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2477_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_toApplicative_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2477_;
goto v_resetjp_2431_;
}
v___jp_2392_:
{
lean_object* v___x_2394_; lean_object* v_rewriteSimpCache_2395_; lean_object* v_rewriteDSimpCache_2396_; lean_object* v_acCache_2397_; lean_object* v_typeAnalysis_2398_; lean_object* v_goal_2399_; lean_object* v_hypotheses_2400_; uint8_t v_didChange_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2412_; 
v___x_2394_ = lean_st_ref_take(v___y_2393_);
v_rewriteSimpCache_2395_ = lean_ctor_get(v___x_2394_, 0);
v_rewriteDSimpCache_2396_ = lean_ctor_get(v___x_2394_, 1);
v_acCache_2397_ = lean_ctor_get(v___x_2394_, 2);
v_typeAnalysis_2398_ = lean_ctor_get(v___x_2394_, 3);
v_goal_2399_ = lean_ctor_get(v___x_2394_, 4);
v_hypotheses_2400_ = lean_ctor_get(v___x_2394_, 5);
v_didChange_2401_ = lean_ctor_get_uint8(v___x_2394_, sizeof(void*)*6);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2403_ = v___x_2394_;
v_isShared_2404_ = v_isSharedCheck_2412_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_hypotheses_2400_);
lean_inc(v_goal_2399_);
lean_inc(v_typeAnalysis_2398_);
lean_inc(v_acCache_2397_);
lean_inc(v_rewriteDSimpCache_2396_);
lean_inc(v_rewriteSimpCache_2395_);
lean_dec(v___x_2394_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2412_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2405_; lean_object* v___x_2407_; 
v___x_2405_ = lean_array_push(v_hypotheses_2400_, v_hyp_2382_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 5, v___x_2405_);
v___x_2407_ = v___x_2403_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_rewriteSimpCache_2395_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_rewriteDSimpCache_2396_);
lean_ctor_set(v_reuseFailAlloc_2411_, 2, v_acCache_2397_);
lean_ctor_set(v_reuseFailAlloc_2411_, 3, v_typeAnalysis_2398_);
lean_ctor_set(v_reuseFailAlloc_2411_, 4, v_goal_2399_);
lean_ctor_set(v_reuseFailAlloc_2411_, 5, v___x_2405_);
lean_ctor_set_uint8(v_reuseFailAlloc_2411_, sizeof(void*)*6, v_didChange_2401_);
v___x_2407_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = lean_st_ref_set(v___y_2393_, v___x_2407_);
v___x_2409_ = lean_box(0);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
}
}
v_resetjp_2431_:
{
lean_object* v_toFunctor_2434_; lean_object* v_toSeq_2435_; lean_object* v_toSeqLeft_2436_; lean_object* v_toSeqRight_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2475_; 
v_toFunctor_2434_ = lean_ctor_get(v_toApplicative_2430_, 0);
v_toSeq_2435_ = lean_ctor_get(v_toApplicative_2430_, 2);
v_toSeqLeft_2436_ = lean_ctor_get(v_toApplicative_2430_, 3);
v_toSeqRight_2437_ = lean_ctor_get(v_toApplicative_2430_, 4);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_toApplicative_2430_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v_toApplicative_2430_, 1);
lean_dec(v_unused_2476_);
v___x_2439_ = v_toApplicative_2430_;
v_isShared_2440_ = v_isSharedCheck_2475_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_toSeqRight_2437_);
lean_inc(v_toSeqLeft_2436_);
lean_inc(v_toSeq_2435_);
lean_inc(v_toFunctor_2434_);
lean_dec(v_toApplicative_2430_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2475_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___f_2441_; lean_object* v___f_2442_; lean_object* v___f_2443_; lean_object* v___f_2444_; lean_object* v___x_2445_; lean_object* v___f_2446_; lean_object* v___f_2447_; lean_object* v___f_2448_; lean_object* v___x_2450_; 
v___f_2441_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4));
v___f_2442_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5));
lean_inc_ref(v_toFunctor_2434_);
v___f_2443_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2443_, 0, v_toFunctor_2434_);
v___f_2444_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2444_, 0, v_toFunctor_2434_);
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___f_2443_);
lean_ctor_set(v___x_2445_, 1, v___f_2444_);
v___f_2446_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2446_, 0, v_toSeqRight_2437_);
v___f_2447_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2447_, 0, v_toSeqLeft_2436_);
v___f_2448_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2448_, 0, v_toSeq_2435_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 4, v___f_2446_);
lean_ctor_set(v___x_2439_, 3, v___f_2447_);
lean_ctor_set(v___x_2439_, 2, v___f_2448_);
lean_ctor_set(v___x_2439_, 1, v___f_2441_);
lean_ctor_set(v___x_2439_, 0, v___x_2445_);
v___x_2450_ = v___x_2439_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___f_2441_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v___f_2448_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v___f_2447_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v___f_2446_);
v___x_2450_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2452_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 1, v___f_2442_);
lean_ctor_set(v___x_2432_, 0, v___x_2450_);
v___x_2452_ = v___x_2432_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v___f_2442_);
v___x_2452_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v_options_2458_; uint8_t v_hasTrace_2459_; 
v___x_2453_ = l_StateRefT_x27_instMonad___redArg(v___x_2452_);
v___x_2454_ = l_ReaderT_instMonad___redArg(v___x_2453_);
v___x_2455_ = l_StateRefT_x27_instMonad___redArg(v___x_2454_);
v___x_2456_ = l_ReaderT_instMonad___redArg(v___x_2455_);
v___x_2457_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13);
v_options_2458_ = lean_ctor_get(v_a_2389_, 2);
v_hasTrace_2459_ = lean_ctor_get_uint8(v_options_2458_, sizeof(void*)*1);
if (v_hasTrace_2459_ == 0)
{
lean_dec_ref(v___x_2456_);
v___y_2393_ = v_a_2384_;
goto v___jp_2392_;
}
else
{
lean_object* v_inheritedTraceOptions_2460_; lean_object* v_cls_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
v_inheritedTraceOptions_2460_ = lean_ctor_get(v_a_2389_, 13);
v_cls_2461_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_2462_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_2463_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2460_, v_options_2458_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_dec_ref(v___x_2456_);
v___y_2393_ = v_a_2384_;
goto v___jp_2392_;
}
else
{
lean_object* v___x_2464_; lean_object* v_toMonadRef_2465_; lean_object* v_type_2466_; lean_object* v___f_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_3853__overap_2471_; lean_object* v___x_2472_; 
v___x_2464_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v_toMonadRef_2465_ = lean_ctor_get(v___x_2464_, 0);
v_type_2466_ = lean_ctor_get(v_hyp_2382_, 1);
v___f_2467_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32);
v___x_2468_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34);
lean_inc_ref(v_type_2466_);
v___x_2469_ = l_Lean_MessageData_ofExpr(v_type_2466_);
v___x_2470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2468_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
lean_inc_ref(v_toMonadRef_2465_);
v___x_3853__overap_2471_ = l_Lean_addTrace___redArg(v___x_2456_, v___x_2457_, v_toMonadRef_2465_, v___f_2467_, v_cls_2461_, v___x_2470_);
lean_inc(v_a_2390_);
lean_inc_ref(v_a_2389_);
lean_inc(v_a_2388_);
lean_inc_ref(v_a_2387_);
lean_inc(v_a_2386_);
lean_inc_ref(v_a_2385_);
lean_inc(v_a_2384_);
lean_inc_ref(v_a_2383_);
v___x_2472_ = lean_apply_9(v___x_3853__overap_2471_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, lean_box(0));
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_dec_ref_known(v___x_2472_, 1);
v___y_2393_ = v_a_2384_;
goto v___jp_2392_;
}
else
{
lean_dec_ref(v_hyp_2382_);
return v___x_2472_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___boxed(lean_object* v_hyp_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp(v_hyp_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(lean_object* v___x_2490_, lean_object* v___f_2491_, lean_object* v___x_2492_, lean_object* v___f_2493_, lean_object* v___x_2494_, lean_object* v___f_2495_, lean_object* v___x_2496_, lean_object* v___x_2497_, lean_object* v_x_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_options_2512_; uint8_t v_hasTrace_2513_; 
v_options_2512_ = lean_ctor_get(v___y_2506_, 2);
v_hasTrace_2513_ = lean_ctor_get_uint8(v_options_2512_, sizeof(void*)*1);
if (v_hasTrace_2513_ == 0)
{
lean_dec_ref(v___y_2499_);
lean_dec_ref(v___x_2497_);
lean_dec_ref(v___x_2496_);
lean_dec(v___f_2495_);
lean_dec(v___x_2494_);
lean_dec(v___f_2493_);
lean_dec(v___x_2492_);
lean_dec(v___f_2491_);
lean_dec(v___x_2490_);
goto v___jp_2509_;
}
else
{
lean_object* v_inheritedTraceOptions_2514_; lean_object* v_cls_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v_inheritedTraceOptions_2514_ = lean_ctor_get(v___y_2506_, 13);
v_cls_2515_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_2516_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_2517_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2514_, v_options_2512_, v___x_2516_);
if (v___x_2517_ == 0)
{
lean_dec_ref(v___y_2499_);
lean_dec_ref(v___x_2497_);
lean_dec_ref(v___x_2496_);
lean_dec(v___f_2495_);
lean_dec(v___x_2494_);
lean_dec(v___f_2493_);
lean_dec(v___x_2492_);
lean_dec(v___f_2491_);
lean_dec(v___x_2490_);
goto v___jp_2509_;
}
else
{
lean_object* v___f_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v_toMonadRef_2527_; lean_object* v_type_2528_; lean_object* v___x_2529_; lean_object* v___f_2530_; lean_object* v___f_2531_; lean_object* v___f_2532_; lean_object* v___f_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_4622__overap_2537_; lean_object* v___x_2538_; 
v___f_2518_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__21));
v___x_2519_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__22));
v___x_2520_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2521_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2519_, v___x_2490_, v___x_2520_);
v___x_2522_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2518_, v___f_2491_, v___x_2521_);
lean_inc(v___x_2492_);
v___x_2523_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2519_, v___x_2492_, v___x_2522_);
lean_inc(v___f_2493_);
v___x_2524_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2518_, v___f_2493_, v___x_2523_);
lean_inc(v___x_2494_);
v___x_2525_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2519_, v___x_2494_, v___x_2524_);
lean_inc(v___f_2495_);
v___x_2526_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2518_, v___f_2495_, v___x_2525_);
v_toMonadRef_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc_ref(v_toMonadRef_2527_);
lean_dec_ref(v___x_2526_);
v_type_2528_ = lean_ctor_get(v___y_2499_, 1);
lean_inc_ref(v_type_2528_);
lean_dec_ref(v___y_2499_);
v___x_2529_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2530_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2530_, 0, v___x_2529_);
lean_closure_set(v___f_2530_, 1, v___x_2492_);
v___f_2531_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2531_, 0, v___f_2530_);
lean_closure_set(v___f_2531_, 1, v___f_2493_);
v___f_2532_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2532_, 0, v___f_2531_);
lean_closure_set(v___f_2532_, 1, v___x_2494_);
v___f_2533_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2533_, 0, v___f_2532_);
lean_closure_set(v___f_2533_, 1, v___f_2495_);
v___x_2534_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__34);
v___x_2535_ = l_Lean_MessageData_ofExpr(v_type_2528_);
v___x_2536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_4622__overap_2537_ = l_Lean_addTrace___redArg(v___x_2496_, v___x_2497_, v_toMonadRef_2527_, v___f_2533_, v_cls_2515_, v___x_2536_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
lean_inc(v___y_2501_);
lean_inc_ref(v___y_2500_);
v___x_2538_ = lean_apply_9(v___x_4622__overap_2537_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, lean_box(0));
return v___x_2538_;
}
}
v___jp_2509_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = lean_box(0);
v___x_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
return v___x_2511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed(lean_object** _args){
lean_object* v___x_2539_ = _args[0];
lean_object* v___f_2540_ = _args[1];
lean_object* v___x_2541_ = _args[2];
lean_object* v___f_2542_ = _args[3];
lean_object* v___x_2543_ = _args[4];
lean_object* v___f_2544_ = _args[5];
lean_object* v___x_2545_ = _args[6];
lean_object* v___x_2546_ = _args[7];
lean_object* v_x_2547_ = _args[8];
lean_object* v___y_2548_ = _args[9];
lean_object* v___y_2549_ = _args[10];
lean_object* v___y_2550_ = _args[11];
lean_object* v___y_2551_ = _args[12];
lean_object* v___y_2552_ = _args[13];
lean_object* v___y_2553_ = _args[14];
lean_object* v___y_2554_ = _args[15];
lean_object* v___y_2555_ = _args[16];
lean_object* v___y_2556_ = _args[17];
lean_object* v___y_2557_ = _args[18];
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0(v___x_2539_, v___f_2540_, v___x_2541_, v___f_2542_, v___x_2543_, v___f_2544_, v___x_2545_, v___x_2546_, v_x_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(lean_object* v_hyps_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v___y_2590_; lean_object* v___x_2591_; lean_object* v_toApplicative_2592_; lean_object* v_toFunctor_2593_; lean_object* v_toSeq_2594_; lean_object* v_toSeqLeft_2595_; lean_object* v_toSeqRight_2596_; lean_object* v___f_2597_; lean_object* v___f_2598_; lean_object* v___f_2599_; lean_object* v___f_2600_; lean_object* v___x_2601_; lean_object* v___f_2602_; lean_object* v___f_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v_toApplicative_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2656_; 
v___x_2591_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1);
v_toApplicative_2592_ = lean_ctor_get(v___x_2591_, 0);
v_toFunctor_2593_ = lean_ctor_get(v_toApplicative_2592_, 0);
v_toSeq_2594_ = lean_ctor_get(v_toApplicative_2592_, 2);
v_toSeqLeft_2595_ = lean_ctor_get(v_toApplicative_2592_, 3);
v_toSeqRight_2596_ = lean_ctor_get(v_toApplicative_2592_, 4);
v___f_2597_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2));
v___f_2598_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3));
lean_inc_ref_n(v_toFunctor_2593_, 2);
v___f_2599_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2599_, 0, v_toFunctor_2593_);
v___f_2600_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2600_, 0, v_toFunctor_2593_);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___f_2599_);
lean_ctor_set(v___x_2601_, 1, v___f_2600_);
lean_inc(v_toSeqRight_2596_);
v___f_2602_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2602_, 0, v_toSeqRight_2596_);
lean_inc(v_toSeqLeft_2595_);
v___f_2603_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2603_, 0, v_toSeqLeft_2595_);
lean_inc(v_toSeq_2594_);
v___f_2604_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2604_, 0, v_toSeq_2594_);
v___x_2605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2601_);
lean_ctor_set(v___x_2605_, 1, v___f_2597_);
lean_ctor_set(v___x_2605_, 2, v___f_2604_);
lean_ctor_set(v___x_2605_, 3, v___f_2603_);
lean_ctor_set(v___x_2605_, 4, v___f_2602_);
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
lean_ctor_set(v___x_2606_, 1, v___f_2598_);
v___x_2607_ = l_StateRefT_x27_instMonad___redArg(v___x_2606_);
v_toApplicative_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; 
v_unused_2657_ = lean_ctor_get(v___x_2607_, 1);
lean_dec(v_unused_2657_);
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2656_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_toApplicative_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2656_;
goto v_resetjp_2609_;
}
v___jp_2569_:
{
lean_object* v___x_2570_; lean_object* v_rewriteSimpCache_2571_; lean_object* v_rewriteDSimpCache_2572_; lean_object* v_acCache_2573_; lean_object* v_typeAnalysis_2574_; lean_object* v_goal_2575_; lean_object* v_hypotheses_2576_; uint8_t v_didChange_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2588_; 
v___x_2570_ = lean_st_ref_take(v_a_2561_);
v_rewriteSimpCache_2571_ = lean_ctor_get(v___x_2570_, 0);
v_rewriteDSimpCache_2572_ = lean_ctor_get(v___x_2570_, 1);
v_acCache_2573_ = lean_ctor_get(v___x_2570_, 2);
v_typeAnalysis_2574_ = lean_ctor_get(v___x_2570_, 3);
v_goal_2575_ = lean_ctor_get(v___x_2570_, 4);
v_hypotheses_2576_ = lean_ctor_get(v___x_2570_, 5);
v_didChange_2577_ = lean_ctor_get_uint8(v___x_2570_, sizeof(void*)*6);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2579_ = v___x_2570_;
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_hypotheses_2576_);
lean_inc(v_goal_2575_);
lean_inc(v_typeAnalysis_2574_);
lean_inc(v_acCache_2573_);
lean_inc(v_rewriteDSimpCache_2572_);
lean_inc(v_rewriteSimpCache_2571_);
lean_dec(v___x_2570_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = l_Array_append___redArg(v_hypotheses_2576_, v_hyps_2559_);
lean_dec_ref(v_hyps_2559_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 5, v___x_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_rewriteSimpCache_2571_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_rewriteDSimpCache_2572_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_acCache_2573_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v_typeAnalysis_2574_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v_goal_2575_);
lean_ctor_set(v_reuseFailAlloc_2587_, 5, v___x_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2587_, sizeof(void*)*6, v_didChange_2577_);
v___x_2583_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_st_ref_set(v_a_2561_, v___x_2583_);
v___x_2585_ = lean_box(0);
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
return v___x_2586_;
}
}
}
v___jp_2589_:
{
if (lean_obj_tag(v___y_2590_) == 0)
{
lean_dec_ref_known(v___y_2590_, 1);
goto v___jp_2569_;
}
else
{
lean_dec_ref(v_hyps_2559_);
return v___y_2590_;
}
}
v_resetjp_2609_:
{
lean_object* v_toFunctor_2612_; lean_object* v_toSeq_2613_; lean_object* v_toSeqLeft_2614_; lean_object* v_toSeqRight_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2654_; 
v_toFunctor_2612_ = lean_ctor_get(v_toApplicative_2608_, 0);
v_toSeq_2613_ = lean_ctor_get(v_toApplicative_2608_, 2);
v_toSeqLeft_2614_ = lean_ctor_get(v_toApplicative_2608_, 3);
v_toSeqRight_2615_ = lean_ctor_get(v_toApplicative_2608_, 4);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_toApplicative_2608_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v_toApplicative_2608_, 1);
lean_dec(v_unused_2655_);
v___x_2617_ = v_toApplicative_2608_;
v_isShared_2618_ = v_isSharedCheck_2654_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_toSeqRight_2615_);
lean_inc(v_toSeqLeft_2614_);
lean_inc(v_toSeq_2613_);
lean_inc(v_toFunctor_2612_);
lean_dec(v_toApplicative_2608_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2654_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___f_2619_; lean_object* v___f_2620_; lean_object* v___f_2621_; lean_object* v___f_2622_; lean_object* v___x_2623_; lean_object* v___f_2624_; lean_object* v___f_2625_; lean_object* v___f_2626_; lean_object* v___x_2628_; 
v___f_2619_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4));
v___f_2620_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5));
lean_inc_ref(v_toFunctor_2612_);
v___f_2621_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2621_, 0, v_toFunctor_2612_);
v___f_2622_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2622_, 0, v_toFunctor_2612_);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___f_2621_);
lean_ctor_set(v___x_2623_, 1, v___f_2622_);
v___f_2624_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2624_, 0, v_toSeqRight_2615_);
v___f_2625_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2625_, 0, v_toSeqLeft_2614_);
v___f_2626_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2626_, 0, v_toSeq_2613_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 4, v___f_2624_);
lean_ctor_set(v___x_2617_, 3, v___f_2625_);
lean_ctor_set(v___x_2617_, 2, v___f_2626_);
lean_ctor_set(v___x_2617_, 1, v___f_2619_);
lean_ctor_set(v___x_2617_, 0, v___x_2623_);
v___x_2628_ = v___x_2617_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___f_2619_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v___f_2626_);
lean_ctor_set(v_reuseFailAlloc_2653_, 3, v___f_2625_);
lean_ctor_set(v_reuseFailAlloc_2653_, 4, v___f_2624_);
v___x_2628_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2630_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 1, v___f_2620_);
lean_ctor_set(v___x_2610_, 0, v___x_2628_);
v___x_2630_ = v___x_2610_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v___f_2620_);
v___x_2630_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___f_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___x_2631_ = l_StateRefT_x27_instMonad___redArg(v___x_2630_);
v___x_2632_ = l_ReaderT_instMonad___redArg(v___x_2631_);
v___x_2633_ = l_StateRefT_x27_instMonad___redArg(v___x_2632_);
v___x_2634_ = l_ReaderT_instMonad___redArg(v___x_2633_);
v___f_2635_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__6));
v___x_2636_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__7));
v___x_2637_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13);
v___x_2638_ = lean_unsigned_to_nat(0u);
v___x_2639_ = lean_array_get_size(v_hyps_2559_);
v___x_2640_ = lean_nat_dec_lt(v___x_2638_, v___x_2639_);
if (v___x_2640_ == 0)
{
lean_dec_ref(v___x_2634_);
goto v___jp_2569_;
}
else
{
lean_object* v___f_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
lean_inc_ref(v___x_2634_);
v___f_2641_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2641_, 0, v___x_2636_);
lean_closure_set(v___f_2641_, 1, v___f_2635_);
lean_closure_set(v___f_2641_, 2, v___x_2636_);
lean_closure_set(v___f_2641_, 3, v___f_2635_);
lean_closure_set(v___f_2641_, 4, v___x_2636_);
lean_closure_set(v___f_2641_, 5, v___f_2635_);
lean_closure_set(v___f_2641_, 6, v___x_2634_);
lean_closure_set(v___f_2641_, 7, v___x_2637_);
v___x_2642_ = lean_box(0);
v___x_2643_ = lean_nat_dec_le(v___x_2639_, v___x_2639_);
if (v___x_2643_ == 0)
{
if (v___x_2640_ == 0)
{
lean_dec_ref(v___f_2641_);
lean_dec_ref(v___x_2634_);
goto v___jp_2569_;
}
else
{
size_t v___x_2644_; size_t v___x_2645_; lean_object* v___x_4298__overap_2646_; lean_object* v___x_2647_; 
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = lean_usize_of_nat(v___x_2639_);
lean_inc_ref(v_hyps_2559_);
v___x_4298__overap_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2634_, v___f_2641_, v_hyps_2559_, v___x_2644_, v___x_2645_, v___x_2642_);
lean_inc(v_a_2567_);
lean_inc_ref(v_a_2566_);
lean_inc(v_a_2565_);
lean_inc_ref(v_a_2564_);
lean_inc(v_a_2563_);
lean_inc_ref(v_a_2562_);
lean_inc(v_a_2561_);
lean_inc_ref(v_a_2560_);
v___x_2647_ = lean_apply_9(v___x_4298__overap_2646_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, lean_box(0));
v___y_2590_ = v___x_2647_;
goto v___jp_2589_;
}
}
else
{
size_t v___x_2648_; size_t v___x_2649_; lean_object* v___x_4302__overap_2650_; lean_object* v___x_2651_; 
v___x_2648_ = ((size_t)0ULL);
v___x_2649_ = lean_usize_of_nat(v___x_2639_);
lean_inc_ref(v_hyps_2559_);
v___x_4302__overap_2650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2634_, v___f_2641_, v_hyps_2559_, v___x_2648_, v___x_2649_, v___x_2642_);
lean_inc(v_a_2567_);
lean_inc_ref(v_a_2566_);
lean_inc(v_a_2565_);
lean_inc_ref(v_a_2564_);
lean_inc(v_a_2563_);
lean_inc_ref(v_a_2562_);
lean_inc(v_a_2561_);
lean_inc_ref(v_a_2560_);
v___x_2651_ = lean_apply_9(v___x_4302__overap_2650_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, lean_box(0));
v___y_2590_ = v___x_2651_;
goto v___jp_2589_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps___boxed(lean_object* v_hyps_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_addHyps(v_hyps_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(lean_object* v_a_2669_){
_start:
{
lean_object* v___x_2671_; lean_object* v_hypotheses_2672_; lean_object* v___x_2673_; 
v___x_2671_ = lean_st_ref_get(v_a_2669_);
v_hypotheses_2672_ = lean_ctor_get(v___x_2671_, 5);
lean_inc_ref(v_hypotheses_2672_);
lean_dec(v___x_2671_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_hypotheses_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg___boxed(lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___redArg(v_a_2674_);
lean_dec(v_a_2674_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v___x_2686_; lean_object* v_hypotheses_2687_; lean_object* v___x_2688_; 
v___x_2686_ = lean_st_ref_get(v_a_2678_);
v_hypotheses_2687_ = lean_ctor_get(v___x_2686_, 5);
lean_inc_ref(v_hypotheses_2687_);
lean_dec(v___x_2686_);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v_hypotheses_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed(lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps(v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(lean_object* v_hyps_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; lean_object* v_rewriteSimpCache_2710_; lean_object* v_rewriteDSimpCache_2711_; lean_object* v_acCache_2712_; lean_object* v_typeAnalysis_2713_; lean_object* v_goal_2714_; uint8_t v_didChange_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2725_; 
v___x_2709_ = lean_st_ref_take(v___y_2701_);
v_rewriteSimpCache_2710_ = lean_ctor_get(v___x_2709_, 0);
v_rewriteDSimpCache_2711_ = lean_ctor_get(v___x_2709_, 1);
v_acCache_2712_ = lean_ctor_get(v___x_2709_, 2);
v_typeAnalysis_2713_ = lean_ctor_get(v___x_2709_, 3);
v_goal_2714_ = lean_ctor_get(v___x_2709_, 4);
v_didChange_2715_ = lean_ctor_get_uint8(v___x_2709_, sizeof(void*)*6);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v___x_2709_, 5);
lean_dec(v_unused_2726_);
v___x_2717_ = v___x_2709_;
v_isShared_2718_ = v_isSharedCheck_2725_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_goal_2714_);
lean_inc(v_typeAnalysis_2713_);
lean_inc(v_acCache_2712_);
lean_inc(v_rewriteDSimpCache_2711_);
lean_inc(v_rewriteSimpCache_2710_);
lean_dec(v___x_2709_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2725_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 5, v_hyps_2699_);
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_rewriteSimpCache_2710_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_rewriteDSimpCache_2711_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v_acCache_2712_);
lean_ctor_set(v_reuseFailAlloc_2724_, 3, v_typeAnalysis_2713_);
lean_ctor_set(v_reuseFailAlloc_2724_, 4, v_goal_2714_);
lean_ctor_set(v_reuseFailAlloc_2724_, 5, v_hyps_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2724_, sizeof(void*)*6, v_didChange_2715_);
v___x_2720_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = lean_st_ref_set(v___y_2701_, v___x_2720_);
v___x_2722_ = lean_box(0);
v___x_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
return v___x_2723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed(lean_object* v_hyps_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0(v_hyps_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1(lean_object* v_inst_2738_, lean_object* v_hyps_2739_){
_start:
{
lean_object* v___f_2740_; lean_object* v___x_2741_; 
v___f_2740_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2740_, 0, v_hyps_2739_);
v___x_2741_ = lean_apply_2(v_inst_2738_, lean_box(0), v___f_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v___x_2751_; lean_object* v_rewriteSimpCache_2752_; lean_object* v_rewriteDSimpCache_2753_; lean_object* v_acCache_2754_; lean_object* v_typeAnalysis_2755_; lean_object* v_goal_2756_; uint8_t v_didChange_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2768_; 
v___x_2751_ = lean_st_ref_take(v___y_2743_);
v_rewriteSimpCache_2752_ = lean_ctor_get(v___x_2751_, 0);
v_rewriteDSimpCache_2753_ = lean_ctor_get(v___x_2751_, 1);
v_acCache_2754_ = lean_ctor_get(v___x_2751_, 2);
v_typeAnalysis_2755_ = lean_ctor_get(v___x_2751_, 3);
v_goal_2756_ = lean_ctor_get(v___x_2751_, 4);
v_didChange_2757_ = lean_ctor_get_uint8(v___x_2751_, sizeof(void*)*6);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2768_ == 0)
{
lean_object* v_unused_2769_; 
v_unused_2769_ = lean_ctor_get(v___x_2751_, 5);
lean_dec(v_unused_2769_);
v___x_2759_ = v___x_2751_;
v_isShared_2760_ = v_isSharedCheck_2768_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_goal_2756_);
lean_inc(v_typeAnalysis_2755_);
lean_inc(v_acCache_2754_);
lean_inc(v_rewriteDSimpCache_2753_);
lean_inc(v_rewriteSimpCache_2752_);
lean_dec(v___x_2751_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2768_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2761_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3));
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 5, v___x_2761_);
v___x_2763_ = v___x_2759_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_rewriteSimpCache_2752_);
lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_rewriteDSimpCache_2753_);
lean_ctor_set(v_reuseFailAlloc_2767_, 2, v_acCache_2754_);
lean_ctor_set(v_reuseFailAlloc_2767_, 3, v_typeAnalysis_2755_);
lean_ctor_set(v_reuseFailAlloc_2767_, 4, v_goal_2756_);
lean_ctor_set(v_reuseFailAlloc_2767_, 5, v___x_2761_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, sizeof(void*)*6, v_didChange_2757_);
v___x_2763_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2764_ = lean_st_ref_set(v___y_2743_, v___x_2763_);
v___x_2765_ = lean_box(0);
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
return v___x_2766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2___boxed(lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__2(v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(lean_object* v_toPure_2780_, lean_object* v_cls_2781_, lean_object* v_____do__lift_2782_, lean_object* v_____do__lift_2783_){
_start:
{
uint8_t v_hasTrace_2784_; 
v_hasTrace_2784_ = lean_ctor_get_uint8(v_____do__lift_2783_, sizeof(void*)*1);
if (v_hasTrace_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec(v_cls_2781_);
v___x_2785_ = lean_box(v_hasTrace_2784_);
v___x_2786_ = lean_apply_2(v_toPure_2780_, lean_box(0), v___x_2785_);
return v___x_2786_;
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2787_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_2788_ = l_Lean_Name_append(v___x_2787_, v_cls_2781_);
v___x_2789_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2782_, v_____do__lift_2783_, v___x_2788_);
lean_dec(v___x_2788_);
v___x_2790_ = lean_box(v___x_2789_);
v___x_2791_ = lean_apply_2(v_toPure_2780_, lean_box(0), v___x_2790_);
return v___x_2791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed(lean_object* v_toPure_2792_, lean_object* v_cls_2793_, lean_object* v_____do__lift_2794_, lean_object* v_____do__lift_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3(v_toPure_2792_, v_cls_2793_, v_____do__lift_2794_, v_____do__lift_2795_);
lean_dec_ref(v_____do__lift_2795_);
lean_dec_ref(v_____do__lift_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4(lean_object* v_toPure_2797_, lean_object* v_cls_2798_, lean_object* v_toBind_2799_, lean_object* v_inst_2800_, lean_object* v_____do__lift_2801_){
_start:
{
lean_object* v___f_2802_; lean_object* v___x_2803_; 
v___f_2802_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_2802_, 0, v_toPure_2797_);
lean_closure_set(v___f_2802_, 1, v_cls_2798_);
lean_closure_set(v___f_2802_, 2, v_____do__lift_2801_);
v___x_2803_ = lean_apply_4(v_toBind_2799_, lean_box(0), lean_box(0), v_inst_2800_, v___f_2802_);
return v___x_2803_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__0));
v___x_2806_ = l_Lean_stringToMessageData(v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(lean_object* v_toPure_2807_, lean_object* v_a_2808_, lean_object* v___y_2809_, lean_object* v_inst_2810_, lean_object* v_inst_2811_, lean_object* v_inst_2812_, lean_object* v_inst_2813_, lean_object* v_cls_2814_, uint8_t v_____do__lift_2815_){
_start:
{
if (v_____do__lift_2815_ == 0)
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
lean_dec(v_cls_2814_);
lean_dec(v_inst_2813_);
lean_dec_ref(v_inst_2812_);
lean_dec_ref(v_inst_2811_);
lean_dec_ref(v_inst_2810_);
lean_dec_ref(v___y_2809_);
lean_dec_ref(v_a_2808_);
v___x_2816_ = lean_box(0);
v___x_2817_ = lean_apply_2(v_toPure_2807_, lean_box(0), v___x_2816_);
return v___x_2817_;
}
else
{
lean_object* v_type_2818_; lean_object* v_type_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec(v_toPure_2807_);
v_type_2818_ = lean_ctor_get(v_a_2808_, 1);
lean_inc_ref(v_type_2818_);
lean_dec_ref(v_a_2808_);
v_type_2819_ = lean_ctor_get(v___y_2809_, 1);
lean_inc_ref(v_type_2819_);
lean_dec_ref(v___y_2809_);
v___x_2820_ = l_Lean_MessageData_ofExpr(v_type_2818_);
v___x_2821_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_2822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2820_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = l_Lean_MessageData_ofExpr(v_type_2819_);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = l_Lean_addTrace___redArg(v_inst_2810_, v_inst_2811_, v_inst_2812_, v_inst_2813_, v_cls_2814_, v___x_2824_);
return v___x_2825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed(lean_object* v_toPure_2826_, lean_object* v_a_2827_, lean_object* v___y_2828_, lean_object* v_inst_2829_, lean_object* v_inst_2830_, lean_object* v_inst_2831_, lean_object* v_inst_2832_, lean_object* v_cls_2833_, lean_object* v_____do__lift_2834_){
_start:
{
uint8_t v_____do__lift_3068__boxed_2835_; lean_object* v_res_2836_; 
v_____do__lift_3068__boxed_2835_ = lean_unbox(v_____do__lift_2834_);
v_res_2836_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5(v_toPure_2826_, v_a_2827_, v___y_2828_, v_inst_2829_, v_inst_2830_, v_inst_2831_, v_inst_2832_, v_cls_2833_, v_____do__lift_3068__boxed_2835_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6(lean_object* v_inst_2837_, lean_object* v_toPure_2838_, lean_object* v_toBind_2839_, lean_object* v_inst_2840_, lean_object* v_a_2841_, lean_object* v_inst_2842_, lean_object* v_inst_2843_, lean_object* v_inst_2844_, lean_object* v_x_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_getInheritedTraceOptions_2847_; lean_object* v_cls_2848_; lean_object* v___f_2849_; lean_object* v___f_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_getInheritedTraceOptions_2847_ = lean_ctor_get(v_inst_2837_, 2);
lean_inc(v_getInheritedTraceOptions_2847_);
v_cls_2848_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
lean_inc_n(v_toBind_2839_, 2);
lean_inc(v_toPure_2838_);
v___f_2849_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2849_, 0, v_toPure_2838_);
lean_closure_set(v___f_2849_, 1, v_cls_2848_);
lean_closure_set(v___f_2849_, 2, v_toBind_2839_);
lean_closure_set(v___f_2849_, 3, v_inst_2840_);
v___f_2850_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_2850_, 0, v_toPure_2838_);
lean_closure_set(v___f_2850_, 1, v_a_2841_);
lean_closure_set(v___f_2850_, 2, v___y_2846_);
lean_closure_set(v___f_2850_, 3, v_inst_2842_);
lean_closure_set(v___f_2850_, 4, v_inst_2837_);
lean_closure_set(v___f_2850_, 5, v_inst_2843_);
lean_closure_set(v___f_2850_, 6, v_inst_2844_);
lean_closure_set(v___f_2850_, 7, v_cls_2848_);
v___x_2851_ = lean_apply_4(v_toBind_2839_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2847_, v___f_2849_);
v___x_2852_ = lean_apply_4(v_toBind_2839_, lean_box(0), lean_box(0), v___x_2851_, v___f_2850_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11(lean_object* v_toPure_2853_, lean_object* v_res_2854_, lean_object* v_____r_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = lean_apply_2(v_toPure_2853_, lean_box(0), v_res_2854_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7(lean_object* v_inst_2857_, lean_object* v_toBind_2858_, lean_object* v___f_2859_, lean_object* v_____r_2860_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2861_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_setDidChange___boxed), 9, 0);
v___x_2862_ = lean_apply_2(v_inst_2857_, lean_box(0), v___x_2861_);
v___x_2863_ = lean_apply_4(v_toBind_2858_, lean_box(0), lean_box(0), v___x_2862_, v___f_2859_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10(lean_object* v___f_2864_, lean_object* v_____r_2865_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = lean_apply_1(v___f_2864_, v_____r_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(lean_object* v___f_2867_, lean_object* v_type_2868_, lean_object* v_type_2869_, lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_inst_2873_, lean_object* v_cls_2874_, lean_object* v_toBind_2875_, lean_object* v___f_2876_, uint8_t v_____do__lift_2877_){
_start:
{
if (v_____do__lift_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
lean_dec(v___f_2876_);
lean_dec(v_toBind_2875_);
lean_dec(v_cls_2874_);
lean_dec(v_inst_2873_);
lean_dec_ref(v_inst_2872_);
lean_dec_ref(v_inst_2871_);
lean_dec_ref(v_inst_2870_);
lean_dec_ref(v_type_2869_);
lean_dec_ref(v_type_2868_);
v___x_2878_ = lean_box(0);
v___x_2879_ = lean_apply_1(v___f_2867_, v___x_2878_);
return v___x_2879_;
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec(v___f_2867_);
v___x_2880_ = l_Lean_MessageData_ofExpr(v_type_2868_);
v___x_2881_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_2883_ = l_Lean_MessageData_ofExpr(v_type_2869_);
v___x_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2882_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = l_Lean_addTrace___redArg(v_inst_2870_, v_inst_2871_, v_inst_2872_, v_inst_2873_, v_cls_2874_, v___x_2884_);
v___x_2886_ = lean_apply_4(v_toBind_2875_, lean_box(0), lean_box(0), v___x_2885_, v___f_2876_);
return v___x_2886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed(lean_object* v___f_2887_, lean_object* v_type_2888_, lean_object* v_type_2889_, lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_cls_2894_, lean_object* v_toBind_2895_, lean_object* v___f_2896_, lean_object* v_____do__lift_2897_){
_start:
{
uint8_t v_____do__lift_3168__boxed_2898_; lean_object* v_res_2899_; 
v_____do__lift_3168__boxed_2898_ = lean_unbox(v_____do__lift_2897_);
v_res_2899_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12(v___f_2887_, v_type_2888_, v_type_2889_, v_inst_2890_, v_inst_2891_, v_inst_2892_, v_inst_2893_, v_cls_2894_, v_toBind_2895_, v___f_2896_, v_____do__lift_3168__boxed_2898_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13(lean_object* v_toPure_2900_, lean_object* v_inst_2901_, lean_object* v_toBind_2902_, lean_object* v_inst_2903_, lean_object* v___f_2904_, lean_object* v_a_2905_, lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v___f_2910_, lean_object* v_res_2911_){
_start:
{
lean_object* v___x_2912_; lean_object* v_zero_2913_; uint8_t v_isZero_2914_; 
v___x_2912_ = lean_array_get_size(v_res_2911_);
v_zero_2913_ = lean_unsigned_to_nat(0u);
v_isZero_2914_ = lean_nat_dec_eq(v___x_2912_, v_zero_2913_);
if (v_isZero_2914_ == 1)
{
lean_object* v___f_2915_; lean_object* v___f_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
lean_dec(v___f_2910_);
lean_dec(v_inst_2909_);
lean_dec_ref(v_inst_2908_);
lean_dec(v_inst_2907_);
lean_dec_ref(v_inst_2906_);
lean_dec_ref(v_a_2905_);
lean_inc_ref(v_res_2911_);
lean_inc(v_toPure_2900_);
v___f_2915_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2915_, 0, v_toPure_2900_);
lean_closure_set(v___f_2915_, 1, v_res_2911_);
lean_inc(v_toBind_2902_);
v___f_2916_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_2916_, 0, v_inst_2901_);
lean_closure_set(v___f_2916_, 1, v_toBind_2902_);
lean_closure_set(v___f_2916_, 2, v___f_2915_);
v___x_2917_ = lean_box(0);
v___x_2918_ = lean_nat_dec_lt(v_zero_2913_, v___x_2912_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
lean_dec_ref(v_res_2911_);
lean_dec(v___f_2904_);
lean_dec_ref(v_inst_2903_);
v___x_2919_ = lean_apply_2(v_toPure_2900_, lean_box(0), v___x_2917_);
v___x_2920_ = lean_apply_4(v_toBind_2902_, lean_box(0), lean_box(0), v___x_2919_, v___f_2916_);
return v___x_2920_;
}
else
{
uint8_t v___x_2921_; 
v___x_2921_ = lean_nat_dec_le(v___x_2912_, v___x_2912_);
if (v___x_2921_ == 0)
{
if (v___x_2918_ == 0)
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
lean_dec_ref(v_res_2911_);
lean_dec(v___f_2904_);
lean_dec_ref(v_inst_2903_);
v___x_2922_ = lean_apply_2(v_toPure_2900_, lean_box(0), v___x_2917_);
v___x_2923_ = lean_apply_4(v_toBind_2902_, lean_box(0), lean_box(0), v___x_2922_, v___f_2916_);
return v___x_2923_;
}
else
{
size_t v___x_2924_; size_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_dec(v_toPure_2900_);
v___x_2924_ = ((size_t)0ULL);
v___x_2925_ = lean_usize_of_nat(v___x_2912_);
v___x_2926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2903_, v___f_2904_, v_res_2911_, v___x_2924_, v___x_2925_, v___x_2917_);
v___x_2927_ = lean_apply_4(v_toBind_2902_, lean_box(0), lean_box(0), v___x_2926_, v___f_2916_);
return v___x_2927_;
}
}
else
{
size_t v___x_2928_; size_t v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec(v_toPure_2900_);
v___x_2928_ = ((size_t)0ULL);
v___x_2929_ = lean_usize_of_nat(v___x_2912_);
v___x_2930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2903_, v___f_2904_, v_res_2911_, v___x_2928_, v___x_2929_, v___x_2917_);
v___x_2931_ = lean_apply_4(v_toBind_2902_, lean_box(0), lean_box(0), v___x_2930_, v___f_2916_);
return v___x_2931_;
}
}
}
else
{
lean_object* v_one_2932_; lean_object* v_n_2933_; uint8_t v_isZero_2934_; 
lean_dec(v___f_2904_);
v_one_2932_ = lean_unsigned_to_nat(1u);
v_n_2933_ = lean_nat_sub(v___x_2912_, v_one_2932_);
v_isZero_2934_ = lean_nat_dec_eq(v_n_2933_, v_zero_2913_);
lean_dec(v_n_2933_);
if (v_isZero_2934_ == 1)
{
lean_object* v_newHyp_2935_; lean_object* v_type_2936_; lean_object* v_type_2937_; uint8_t v___x_2938_; 
lean_dec(v___f_2910_);
v_newHyp_2935_ = lean_array_fget_borrowed(v_res_2911_, v_zero_2913_);
v_type_2936_ = lean_ctor_get(v_newHyp_2935_, 1);
v_type_2937_ = lean_ctor_get(v_a_2905_, 1);
lean_inc_ref(v_type_2937_);
lean_dec_ref(v_a_2905_);
v___x_2938_ = lean_expr_eqv(v_type_2936_, v_type_2937_);
if (v___x_2938_ == 0)
{
lean_object* v_getInheritedTraceOptions_2939_; lean_object* v___f_2940_; lean_object* v___f_2941_; lean_object* v___f_2942_; lean_object* v_cls_2943_; lean_object* v___f_2944_; lean_object* v___f_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
lean_inc_ref(v_type_2936_);
v_getInheritedTraceOptions_2939_ = lean_ctor_get(v_inst_2906_, 2);
lean_inc(v_getInheritedTraceOptions_2939_);
lean_inc(v_toPure_2900_);
v___f_2940_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2940_, 0, v_toPure_2900_);
lean_closure_set(v___f_2940_, 1, v_res_2911_);
lean_inc_n(v_toBind_2902_, 4);
v___f_2941_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_2941_, 0, v_inst_2901_);
lean_closure_set(v___f_2941_, 1, v_toBind_2902_);
lean_closure_set(v___f_2941_, 2, v___f_2940_);
lean_inc_ref(v___f_2941_);
v___f_2942_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_2942_, 0, v___f_2941_);
v_cls_2943_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___f_2944_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__4), 5, 4);
lean_closure_set(v___f_2944_, 0, v_toPure_2900_);
lean_closure_set(v___f_2944_, 1, v_cls_2943_);
lean_closure_set(v___f_2944_, 2, v_toBind_2902_);
lean_closure_set(v___f_2944_, 3, v_inst_2907_);
v___f_2945_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_2945_, 0, v___f_2941_);
lean_closure_set(v___f_2945_, 1, v_type_2937_);
lean_closure_set(v___f_2945_, 2, v_type_2936_);
lean_closure_set(v___f_2945_, 3, v_inst_2903_);
lean_closure_set(v___f_2945_, 4, v_inst_2906_);
lean_closure_set(v___f_2945_, 5, v_inst_2908_);
lean_closure_set(v___f_2945_, 6, v_inst_2909_);
lean_closure_set(v___f_2945_, 7, v_cls_2943_);
lean_closure_set(v___f_2945_, 8, v_toBind_2902_);
lean_closure_set(v___f_2945_, 9, v___f_2942_);
v___x_2946_ = lean_apply_4(v_toBind_2902_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_2939_, v___f_2944_);
v___x_2947_ = lean_apply_4(v_toBind_2902_, lean_box(0), lean_box(0), v___x_2946_, v___f_2945_);
return v___x_2947_;
}
else
{
lean_object* v___x_2948_; 
lean_dec_ref(v_type_2937_);
lean_dec(v_inst_2909_);
lean_dec_ref(v_inst_2908_);
lean_dec(v_inst_2907_);
lean_dec_ref(v_inst_2906_);
lean_dec_ref(v_inst_2903_);
lean_dec(v_toBind_2902_);
lean_dec(v_inst_2901_);
v___x_2948_ = lean_apply_2(v_toPure_2900_, lean_box(0), v_res_2911_);
return v___x_2948_;
}
}
else
{
lean_object* v___f_2949_; lean_object* v___f_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
lean_dec(v_inst_2909_);
lean_dec_ref(v_inst_2908_);
lean_dec(v_inst_2907_);
lean_dec_ref(v_inst_2906_);
lean_dec_ref(v_a_2905_);
lean_inc_ref(v_res_2911_);
lean_inc(v_toPure_2900_);
v___f_2949_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__11), 3, 2);
lean_closure_set(v___f_2949_, 0, v_toPure_2900_);
lean_closure_set(v___f_2949_, 1, v_res_2911_);
lean_inc(v_toBind_2902_);
v___f_2950_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_2950_, 0, v_inst_2901_);
lean_closure_set(v___f_2950_, 1, v_toBind_2902_);
lean_closure_set(v___f_2950_, 2, v___f_2949_);
v___x_2951_ = lean_box(0);
v___x_2952_ = lean_nat_dec_lt(v_zero_2913_, v___x_2912_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec_ref(v_res_2911_);
lean_dec(v___f_2910_);
lean_dec_ref(v_inst_2903_);
v___x_2953_ = lean_apply_2(v_toPure_2900_, lean_box(0), v___x_2951_);
v___x_2954_ = lean_apply_4(v_toBind_2902_, lean_box(0), lean_box(0), v___x_2953_, v___f_2950_);
return v___x_2954_;
}
else
{
uint8_t v___x_2955_; 
v___x_2955_ = lean_nat_dec_le(v___x_2912_, v___x_2912_);
if (v___x_2955_ == 0)
{
if (v___x_2952_ == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_dec_ref(v_res_2911_);
lean_dec(v___f_2910_);
lean_dec_ref(v_inst_2903_);
v___x_2956_ = lean_apply_2(v_toPure_2900_, lean_box(0), v___x_2951_);
v___x_2957_ = lean_apply_4(v_toBind_2902_, lean_box(0), lean_box(0), v___x_2956_, v___f_2950_);
return v___x_2957_;
}
else
{
size_t v___x_2958_; size_t v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
lean_dec(v_toPure_2900_);
v___x_2958_ = ((size_t)0ULL);
v___x_2959_ = lean_usize_of_nat(v___x_2912_);
v___x_2960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2903_, v___f_2910_, v_res_2911_, v___x_2958_, v___x_2959_, v___x_2951_);
v___x_2961_ = lean_apply_4(v_toBind_2902_, lean_box(0), lean_box(0), v___x_2960_, v___f_2950_);
return v___x_2961_;
}
}
else
{
size_t v___x_2962_; size_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v_toPure_2900_);
v___x_2962_ = ((size_t)0ULL);
v___x_2963_ = lean_usize_of_nat(v___x_2912_);
v___x_2964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2903_, v___f_2910_, v_res_2911_, v___x_2962_, v___x_2963_, v___x_2951_);
v___x_2965_ = lean_apply_4(v_toBind_2902_, lean_box(0), lean_box(0), v___x_2964_, v___f_2950_);
return v___x_2965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(lean_object* v_bs_2966_, lean_object* v_toPure_2967_, lean_object* v_____do__lift_2968_){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = l_Array_append___redArg(v_bs_2966_, v_____do__lift_2968_);
v___x_2970_ = lean_apply_2(v_toPure_2967_, lean_box(0), v___x_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed(lean_object* v_bs_2971_, lean_object* v_toPure_2972_, lean_object* v_____do__lift_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8(v_bs_2971_, v_toPure_2972_, v_____do__lift_2973_);
lean_dec_ref(v_____do__lift_2973_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9(lean_object* v_inst_2975_, lean_object* v_toPure_2976_, lean_object* v_toBind_2977_, lean_object* v_inst_2978_, lean_object* v_inst_2979_, lean_object* v_inst_2980_, lean_object* v_inst_2981_, lean_object* v_inst_2982_, lean_object* v_f_2983_, lean_object* v_bs_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___f_2986_; lean_object* v___f_2987_; lean_object* v___f_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
lean_inc(v_inst_2981_);
lean_inc_ref(v_inst_2980_);
lean_inc_ref(v_inst_2979_);
lean_inc_ref_n(v_a_2985_, 2);
lean_inc(v_inst_2978_);
lean_inc_n(v_toBind_2977_, 3);
lean_inc_n(v_toPure_2976_, 2);
lean_inc_ref(v_inst_2975_);
v___f_2986_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__6), 10, 8);
lean_closure_set(v___f_2986_, 0, v_inst_2975_);
lean_closure_set(v___f_2986_, 1, v_toPure_2976_);
lean_closure_set(v___f_2986_, 2, v_toBind_2977_);
lean_closure_set(v___f_2986_, 3, v_inst_2978_);
lean_closure_set(v___f_2986_, 4, v_a_2985_);
lean_closure_set(v___f_2986_, 5, v_inst_2979_);
lean_closure_set(v___f_2986_, 6, v_inst_2980_);
lean_closure_set(v___f_2986_, 7, v_inst_2981_);
lean_inc_ref(v___f_2986_);
v___f_2987_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__13), 12, 11);
lean_closure_set(v___f_2987_, 0, v_toPure_2976_);
lean_closure_set(v___f_2987_, 1, v_inst_2982_);
lean_closure_set(v___f_2987_, 2, v_toBind_2977_);
lean_closure_set(v___f_2987_, 3, v_inst_2979_);
lean_closure_set(v___f_2987_, 4, v___f_2986_);
lean_closure_set(v___f_2987_, 5, v_a_2985_);
lean_closure_set(v___f_2987_, 6, v_inst_2975_);
lean_closure_set(v___f_2987_, 7, v_inst_2978_);
lean_closure_set(v___f_2987_, 8, v_inst_2980_);
lean_closure_set(v___f_2987_, 9, v_inst_2981_);
lean_closure_set(v___f_2987_, 10, v___f_2986_);
v___f_2988_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__8___boxed), 3, 2);
lean_closure_set(v___f_2988_, 0, v_bs_2984_);
lean_closure_set(v___f_2988_, 1, v_toPure_2976_);
v___x_2989_ = lean_apply_1(v_f_2983_, v_a_2985_);
v___x_2990_ = lean_apply_4(v_toBind_2977_, lean_box(0), lean_box(0), v___x_2989_, v___f_2987_);
v___x_2991_ = lean_apply_4(v_toBind_2977_, lean_box(0), lean_box(0), v___x_2990_, v___f_2988_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14(lean_object* v_hyps_2994_, lean_object* v_toPure_2995_, lean_object* v_toBind_2996_, lean_object* v___f_2997_, lean_object* v_inst_2998_, lean_object* v___f_2999_, lean_object* v_____r_3000_){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3001_ = lean_unsigned_to_nat(0u);
v___x_3002_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14___closed__0));
v___x_3003_ = lean_array_get_size(v_hyps_2994_);
v___x_3004_ = lean_nat_dec_lt(v___x_3001_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
lean_dec(v___f_2999_);
lean_dec_ref(v_inst_2998_);
lean_dec_ref(v_hyps_2994_);
v___x_3005_ = lean_apply_2(v_toPure_2995_, lean_box(0), v___x_3002_);
v___x_3006_ = lean_apply_4(v_toBind_2996_, lean_box(0), lean_box(0), v___x_3005_, v___f_2997_);
return v___x_3006_;
}
else
{
uint8_t v___x_3007_; 
v___x_3007_ = lean_nat_dec_le(v___x_3003_, v___x_3003_);
if (v___x_3007_ == 0)
{
if (v___x_3004_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec(v___f_2999_);
lean_dec_ref(v_inst_2998_);
lean_dec_ref(v_hyps_2994_);
v___x_3008_ = lean_apply_2(v_toPure_2995_, lean_box(0), v___x_3002_);
v___x_3009_ = lean_apply_4(v_toBind_2996_, lean_box(0), lean_box(0), v___x_3008_, v___f_2997_);
return v___x_3009_;
}
else
{
size_t v___x_3010_; size_t v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
lean_dec(v_toPure_2995_);
v___x_3010_ = ((size_t)0ULL);
v___x_3011_ = lean_usize_of_nat(v___x_3003_);
v___x_3012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2998_, v___f_2999_, v_hyps_2994_, v___x_3010_, v___x_3011_, v___x_3002_);
v___x_3013_ = lean_apply_4(v_toBind_2996_, lean_box(0), lean_box(0), v___x_3012_, v___f_2997_);
return v___x_3013_;
}
}
else
{
size_t v___x_3014_; size_t v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
lean_dec(v_toPure_2995_);
v___x_3014_ = ((size_t)0ULL);
v___x_3015_ = lean_usize_of_nat(v___x_3003_);
v___x_3016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_2998_, v___f_2999_, v_hyps_2994_, v___x_3014_, v___x_3015_, v___x_3002_);
v___x_3017_ = lean_apply_4(v_toBind_2996_, lean_box(0), lean_box(0), v___x_3016_, v___f_2997_);
return v___x_3017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15(lean_object* v_toPure_3018_, lean_object* v_toBind_3019_, lean_object* v___f_3020_, lean_object* v_inst_3021_, lean_object* v___f_3022_, lean_object* v_inst_3023_, lean_object* v___f_3024_, lean_object* v_hyps_3025_){
_start:
{
lean_object* v___f_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
lean_inc(v_toBind_3019_);
v___f_3026_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__14), 7, 6);
lean_closure_set(v___f_3026_, 0, v_hyps_3025_);
lean_closure_set(v___f_3026_, 1, v_toPure_3018_);
lean_closure_set(v___f_3026_, 2, v_toBind_3019_);
lean_closure_set(v___f_3026_, 3, v___f_3020_);
lean_closure_set(v___f_3026_, 4, v_inst_3021_);
lean_closure_set(v___f_3026_, 5, v___f_3022_);
v___x_3027_ = lean_apply_2(v_inst_3023_, lean_box(0), v___f_3024_);
v___x_3028_ = lean_apply_4(v_toBind_3019_, lean_box(0), lean_box(0), v___x_3027_, v___f_3026_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg(lean_object* v_inst_3030_, lean_object* v_inst_3031_, lean_object* v_inst_3032_, lean_object* v_inst_3033_, lean_object* v_inst_3034_, lean_object* v_inst_3035_, lean_object* v_f_3036_){
_start:
{
lean_object* v_toApplicative_3037_; lean_object* v_toBind_3038_; lean_object* v_toPure_3039_; lean_object* v___f_3040_; lean_object* v___f_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___f_3044_; lean_object* v___f_3045_; lean_object* v___x_3046_; 
v_toApplicative_3037_ = lean_ctor_get(v_inst_3030_, 0);
v_toBind_3038_ = lean_ctor_get(v_inst_3030_, 1);
lean_inc_n(v_toBind_3038_, 3);
v_toPure_3039_ = lean_ctor_get(v_toApplicative_3037_, 1);
lean_inc_n(v_toPure_3039_, 2);
lean_inc_n(v_inst_3035_, 3);
v___f_3040_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3040_, 0, v_inst_3035_);
v___f_3041_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3042_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
v___x_3043_ = lean_apply_2(v_inst_3035_, lean_box(0), v___x_3042_);
lean_inc_ref(v_inst_3030_);
v___f_3044_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3044_, 0, v_inst_3031_);
lean_closure_set(v___f_3044_, 1, v_toPure_3039_);
lean_closure_set(v___f_3044_, 2, v_toBind_3038_);
lean_closure_set(v___f_3044_, 3, v_inst_3032_);
lean_closure_set(v___f_3044_, 4, v_inst_3030_);
lean_closure_set(v___f_3044_, 5, v_inst_3034_);
lean_closure_set(v___f_3044_, 6, v_inst_3033_);
lean_closure_set(v___f_3044_, 7, v_inst_3035_);
lean_closure_set(v___f_3044_, 8, v_f_3036_);
v___f_3045_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3045_, 0, v_toPure_3039_);
lean_closure_set(v___f_3045_, 1, v_toBind_3038_);
lean_closure_set(v___f_3045_, 2, v___f_3040_);
lean_closure_set(v___f_3045_, 3, v_inst_3030_);
lean_closure_set(v___f_3045_, 4, v___f_3044_);
lean_closure_set(v___f_3045_, 5, v_inst_3035_);
lean_closure_set(v___f_3045_, 6, v___f_3041_);
v___x_3046_ = lean_apply_4(v_toBind_3038_, lean_box(0), lean_box(0), v___x_3043_, v___f_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps(lean_object* v_m_3047_, lean_object* v_inst_3048_, lean_object* v_inst_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_f_3054_){
_start:
{
lean_object* v_toApplicative_3055_; lean_object* v_toBind_3056_; lean_object* v_toPure_3057_; lean_object* v___f_3058_; lean_object* v___f_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___f_3062_; lean_object* v___f_3063_; lean_object* v___x_3064_; 
v_toApplicative_3055_ = lean_ctor_get(v_inst_3048_, 0);
v_toBind_3056_ = lean_ctor_get(v_inst_3048_, 1);
lean_inc_n(v_toBind_3056_, 3);
v_toPure_3057_ = lean_ctor_get(v_toApplicative_3055_, 1);
lean_inc_n(v_toPure_3057_, 2);
lean_inc_n(v_inst_3053_, 3);
v___f_3058_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3058_, 0, v_inst_3053_);
v___f_3059_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___closed__0));
v___x_3060_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
v___x_3061_ = lean_apply_2(v_inst_3053_, lean_box(0), v___x_3060_);
lean_inc_ref(v_inst_3048_);
v___f_3062_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__9), 11, 9);
lean_closure_set(v___f_3062_, 0, v_inst_3049_);
lean_closure_set(v___f_3062_, 1, v_toPure_3057_);
lean_closure_set(v___f_3062_, 2, v_toBind_3056_);
lean_closure_set(v___f_3062_, 3, v_inst_3050_);
lean_closure_set(v___f_3062_, 4, v_inst_3048_);
lean_closure_set(v___f_3062_, 5, v_inst_3052_);
lean_closure_set(v___f_3062_, 6, v_inst_3051_);
lean_closure_set(v___f_3062_, 7, v_inst_3053_);
lean_closure_set(v___f_3062_, 8, v_f_3054_);
v___f_3063_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__15), 8, 7);
lean_closure_set(v___f_3063_, 0, v_toPure_3057_);
lean_closure_set(v___f_3063_, 1, v_toBind_3056_);
lean_closure_set(v___f_3063_, 2, v___f_3058_);
lean_closure_set(v___f_3063_, 3, v_inst_3048_);
lean_closure_set(v___f_3063_, 4, v___f_3062_);
lean_closure_set(v___f_3063_, 5, v_inst_3053_);
lean_closure_set(v___f_3063_, 6, v___f_3059_);
v___x_3064_ = lean_apply_4(v_toBind_3056_, lean_box(0), lean_box(0), v___x_3061_, v___f_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0(lean_object* v_toPure_3065_, lean_object* v_____do__lift_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = lean_apply_2(v_toPure_3065_, lean_box(0), v_____do__lift_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1(lean_object* v_toPure_3068_, lean_object* v_____r_3069_){
_start:
{
uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = 0;
v___x_3071_ = lean_box(v___x_3070_);
v___x_3072_ = lean_apply_2(v_toPure_3068_, lean_box(0), v___x_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(lean_object* v_snd_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v___x_3083_; lean_object* v_rewriteSimpCache_3084_; lean_object* v_rewriteDSimpCache_3085_; lean_object* v_acCache_3086_; lean_object* v_typeAnalysis_3087_; lean_object* v_goal_3088_; uint8_t v_didChange_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3099_; 
v___x_3083_ = lean_st_ref_take(v___y_3075_);
v_rewriteSimpCache_3084_ = lean_ctor_get(v___x_3083_, 0);
v_rewriteDSimpCache_3085_ = lean_ctor_get(v___x_3083_, 1);
v_acCache_3086_ = lean_ctor_get(v___x_3083_, 2);
v_typeAnalysis_3087_ = lean_ctor_get(v___x_3083_, 3);
v_goal_3088_ = lean_ctor_get(v___x_3083_, 4);
v_didChange_3089_ = lean_ctor_get_uint8(v___x_3083_, sizeof(void*)*6);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v___x_3083_, 5);
lean_dec(v_unused_3100_);
v___x_3091_ = v___x_3083_;
v_isShared_3092_ = v_isSharedCheck_3099_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_goal_3088_);
lean_inc(v_typeAnalysis_3087_);
lean_inc(v_acCache_3086_);
lean_inc(v_rewriteDSimpCache_3085_);
lean_inc(v_rewriteSimpCache_3084_);
lean_dec(v___x_3083_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3099_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 5, v_snd_3073_);
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_rewriteSimpCache_3084_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_rewriteDSimpCache_3085_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_acCache_3086_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_typeAnalysis_3087_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_goal_3088_);
lean_ctor_set(v_reuseFailAlloc_3098_, 5, v_snd_3073_);
lean_ctor_set_uint8(v_reuseFailAlloc_3098_, sizeof(void*)*6, v_didChange_3089_);
v___x_3094_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = lean_st_ref_set(v___y_3075_, v___x_3094_);
v___x_3096_ = lean_box(0);
v___x_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
return v___x_3097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed(lean_object* v_snd_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2(v_snd_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3(lean_object* v_inst_3112_, lean_object* v_toBind_3113_, lean_object* v___f_3114_, lean_object* v_toPure_3115_, lean_object* v_____s_3116_){
_start:
{
lean_object* v_fst_3117_; 
v_fst_3117_ = lean_ctor_get(v_____s_3116_, 0);
if (lean_obj_tag(v_fst_3117_) == 0)
{
lean_object* v_snd_3118_; lean_object* v___f_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
lean_dec(v_toPure_3115_);
v_snd_3118_ = lean_ctor_get(v_____s_3116_, 1);
lean_inc(v_snd_3118_);
lean_dec_ref(v_____s_3116_);
v___f_3119_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__2___boxed), 10, 1);
lean_closure_set(v___f_3119_, 0, v_snd_3118_);
v___x_3120_ = lean_apply_2(v_inst_3112_, lean_box(0), v___f_3119_);
v___x_3121_ = lean_apply_4(v_toBind_3113_, lean_box(0), lean_box(0), v___x_3120_, v___f_3114_);
return v___x_3121_;
}
else
{
lean_object* v_val_3122_; lean_object* v___x_3123_; 
lean_inc_ref(v_fst_3117_);
lean_dec_ref(v_____s_3116_);
lean_dec(v___f_3114_);
lean_dec(v_toBind_3113_);
lean_dec(v_inst_3112_);
v_val_3122_ = lean_ctor_get(v_fst_3117_, 0);
lean_inc(v_val_3122_);
lean_dec_ref_known(v_fst_3117_, 1);
v___x_3123_ = lean_apply_2(v_toPure_3115_, lean_box(0), v_val_3122_);
return v___x_3123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(lean_object* v_toPure_3124_, lean_object* v_next_3125_, lean_object* v_G_3126_, lean_object* v_____do__lift_3127_){
_start:
{
if (lean_obj_tag(v_____do__lift_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3129_; 
lean_dec(v_G_3126_);
v_a_3128_ = lean_ctor_get(v_____do__lift_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v_____do__lift_3127_, 1);
v___x_3129_ = lean_apply_2(v_toPure_3124_, lean_box(0), v_a_3128_);
return v___x_3129_;
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_dec(v_toPure_3124_);
v_a_3130_ = lean_ctor_get(v_____do__lift_3127_, 0);
lean_inc(v_a_3130_);
lean_dec_ref_known(v_____do__lift_3127_, 1);
v___x_3131_ = lean_unsigned_to_nat(1u);
v___x_3132_ = lean_nat_add(v_next_3125_, v___x_3131_);
v___x_3133_ = lean_apply_4(v_G_3126_, v___x_3132_, v_a_3130_, lean_box(0), lean_box(0));
return v___x_3133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed(lean_object* v_toPure_3134_, lean_object* v_next_3135_, lean_object* v_G_3136_, lean_object* v_____do__lift_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4(v_toPure_3134_, v_next_3135_, v_G_3136_, v_____do__lift_3137_);
lean_dec(v_next_3135_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(lean_object* v_snd_3139_, lean_object* v_newHyp_3140_, lean_object* v___x_3141_, lean_object* v_toPure_3142_, lean_object* v_____r_3143_){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3144_ = lean_array_push(v_snd_3139_, v_newHyp_3140_);
v___x_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3141_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
v___x_3147_ = lean_apply_2(v_toPure_3142_, lean_box(0), v___x_3146_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(lean_object* v_toPure_3148_, lean_object* v___x_3149_, lean_object* v_____do__lift_3150_, lean_object* v_____do__lift_3151_){
_start:
{
uint8_t v_hasTrace_3152_; 
v_hasTrace_3152_ = lean_ctor_get_uint8(v_____do__lift_3151_, sizeof(void*)*1);
if (v_hasTrace_3152_ == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_dec(v___x_3149_);
v___x_3153_ = lean_box(v_hasTrace_3152_);
v___x_3154_ = lean_apply_2(v_toPure_3148_, lean_box(0), v___x_3153_);
return v___x_3154_;
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3155_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__19));
v___x_3156_ = l_Lean_Name_append(v___x_3155_, v___x_3149_);
v___x_3157_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_3150_, v_____do__lift_3151_, v___x_3156_);
lean_dec(v___x_3156_);
v___x_3158_ = lean_box(v___x_3157_);
v___x_3159_ = lean_apply_2(v_toPure_3148_, lean_box(0), v___x_3158_);
return v___x_3159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed(lean_object* v_toPure_3160_, lean_object* v___x_3161_, lean_object* v_____do__lift_3162_, lean_object* v_____do__lift_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9(v_toPure_3160_, v___x_3161_, v_____do__lift_3162_, v_____do__lift_3163_);
lean_dec_ref(v_____do__lift_3163_);
lean_dec_ref(v_____do__lift_3162_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6(lean_object* v_toPure_3165_, lean_object* v___x_3166_, lean_object* v_toBind_3167_, lean_object* v_inst_3168_, lean_object* v_____do__lift_3169_){
_start:
{
lean_object* v___f_3170_; lean_object* v___x_3171_; 
v___f_3170_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__9___boxed), 4, 3);
lean_closure_set(v___f_3170_, 0, v_toPure_3165_);
lean_closure_set(v___f_3170_, 1, v___x_3166_);
lean_closure_set(v___f_3170_, 2, v_____do__lift_3169_);
v___x_3171_ = lean_apply_4(v_toBind_3167_, lean_box(0), lean_box(0), v_inst_3168_, v___f_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(lean_object* v___f_3172_, lean_object* v_inst_3173_, lean_object* v___x_3174_, lean_object* v_type_3175_, lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_inst_3178_, lean_object* v___x_3179_, lean_object* v_toBind_3180_, lean_object* v___f_3181_, uint8_t v_____do__lift_3182_){
_start:
{
if (v_____do__lift_3182_ == 0)
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
lean_dec(v___f_3181_);
lean_dec(v_toBind_3180_);
lean_dec(v___x_3179_);
lean_dec(v_inst_3178_);
lean_dec_ref(v_inst_3177_);
lean_dec_ref(v_inst_3176_);
lean_dec_ref(v_type_3175_);
lean_dec_ref(v___x_3174_);
lean_dec_ref(v_inst_3173_);
v___x_3183_ = lean_box(0);
v___x_3184_ = lean_apply_1(v___f_3172_, v___x_3183_);
return v___x_3184_;
}
else
{
lean_object* v_toMonadRef_3185_; lean_object* v_type_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
lean_dec(v___f_3172_);
v_toMonadRef_3185_ = lean_ctor_get(v_inst_3173_, 1);
lean_inc_ref(v_toMonadRef_3185_);
lean_dec_ref(v_inst_3173_);
v_type_3186_ = lean_ctor_get(v___x_3174_, 1);
lean_inc_ref(v_type_3186_);
lean_dec_ref(v___x_3174_);
v___x_3187_ = l_Lean_MessageData_ofExpr(v_type_3186_);
v___x_3188_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
v___x_3189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3187_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = l_Lean_MessageData_ofExpr(v_type_3175_);
v___x_3191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3189_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = l_Lean_addTrace___redArg(v_inst_3176_, v_inst_3177_, v_toMonadRef_3185_, v_inst_3178_, v___x_3179_, v___x_3191_);
v___x_3193_ = lean_apply_4(v_toBind_3180_, lean_box(0), lean_box(0), v___x_3192_, v___f_3181_);
return v___x_3193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed(lean_object* v___f_3194_, lean_object* v_inst_3195_, lean_object* v___x_3196_, lean_object* v_type_3197_, lean_object* v_inst_3198_, lean_object* v_inst_3199_, lean_object* v_inst_3200_, lean_object* v___x_3201_, lean_object* v_toBind_3202_, lean_object* v___f_3203_, lean_object* v_____do__lift_3204_){
_start:
{
uint8_t v_____do__lift_1962__boxed_3205_; lean_object* v_res_3206_; 
v_____do__lift_1962__boxed_3205_ = lean_unbox(v_____do__lift_3204_);
v_res_3206_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7(v___f_3194_, v_inst_3195_, v___x_3196_, v_type_3197_, v_inst_3198_, v_inst_3199_, v_inst_3200_, v___x_3201_, v_toBind_3202_, v___f_3203_, v_____do__lift_1962__boxed_3205_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(uint8_t v___x_3207_, lean_object* v_snd_3208_, lean_object* v_toPure_3209_, lean_object* v_____r_3210_){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3211_ = lean_box(v___x_3207_);
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
lean_ctor_set(v___x_3213_, 1, v_snd_3208_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
v___x_3215_ = lean_apply_2(v_toPure_3209_, lean_box(0), v___x_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed(lean_object* v___x_3216_, lean_object* v_snd_3217_, lean_object* v_toPure_3218_, lean_object* v_____r_3219_){
_start:
{
uint8_t v___x_2000__boxed_3220_; lean_object* v_res_3221_; 
v___x_2000__boxed_3220_ = lean_unbox(v___x_3216_);
v_res_3221_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8(v___x_2000__boxed_3220_, v_snd_3217_, v_toPure_3218_, v_____r_3219_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10(lean_object* v_inst_3222_, lean_object* v_value_3223_, lean_object* v_toBind_3224_, lean_object* v___f_3225_, lean_object* v_____do__lift_3226_){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = l_Lean_MVarId_assign___redArg(v_inst_3222_, v_____do__lift_3226_, v_value_3223_);
v___x_3228_ = lean_apply_4(v_toBind_3224_, lean_box(0), lean_box(0), v___x_3227_, v___f_3225_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11(lean_object* v___x_3229_, lean_object* v_snd_3230_, lean_object* v___x_3231_, lean_object* v_toPure_3232_, lean_object* v_inst_3233_, lean_object* v_toBind_3234_, lean_object* v_inst_3235_, lean_object* v_inst_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_inst_3239_, lean_object* v_inst_3240_, lean_object* v_newHyp_3241_){
_start:
{
lean_object* v_type_3242_; lean_object* v_value_3243_; uint8_t v___x_3244_; 
v_type_3242_ = lean_ctor_get(v_newHyp_3241_, 1);
v_value_3243_ = lean_ctor_get(v_newHyp_3241_, 2);
lean_inc_ref(v_type_3242_);
v___x_3244_ = l_Lean_Expr_isFalse(v_type_3242_);
if (v___x_3244_ == 0)
{
lean_object* v_type_3245_; lean_object* v___f_3246_; lean_object* v___f_3247_; lean_object* v___f_3248_; lean_object* v___f_3249_; uint8_t v___x_3257_; 
lean_dec_ref(v_inst_3240_);
v_type_3245_ = lean_ctor_get(v___x_3229_, 1);
lean_inc(v_toPure_3232_);
lean_inc(v___x_3231_);
lean_inc_ref(v_newHyp_3241_);
lean_inc(v_snd_3230_);
v___f_3246_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5), 5, 4);
lean_closure_set(v___f_3246_, 0, v_snd_3230_);
lean_closure_set(v___f_3246_, 1, v_newHyp_3241_);
lean_closure_set(v___f_3246_, 2, v___x_3231_);
lean_closure_set(v___f_3246_, 3, v_toPure_3232_);
v___f_3247_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3247_, 0, v___f_3246_);
lean_inc(v_toBind_3234_);
v___f_3248_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3248_, 0, v_inst_3233_);
lean_closure_set(v___f_3248_, 1, v_toBind_3234_);
lean_closure_set(v___f_3248_, 2, v___f_3247_);
lean_inc_ref(v___f_3248_);
v___f_3249_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3249_, 0, v___f_3248_);
v___x_3257_ = lean_expr_eqv(v_type_3245_, v_type_3242_);
if (v___x_3257_ == 0)
{
lean_inc_ref(v_type_3242_);
lean_dec_ref(v_newHyp_3241_);
lean_dec(v___x_3231_);
lean_dec(v_snd_3230_);
goto v___jp_3250_;
}
else
{
if (v___x_3244_ == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_dec_ref(v___f_3249_);
lean_dec_ref(v___f_3248_);
lean_dec(v_inst_3239_);
lean_dec_ref(v_inst_3238_);
lean_dec_ref(v_inst_3237_);
lean_dec(v_inst_3236_);
lean_dec_ref(v_inst_3235_);
lean_dec(v_toBind_3234_);
lean_dec_ref(v___x_3229_);
v___x_3258_ = lean_box(0);
v___x_3259_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v_snd_3230_, v_newHyp_3241_, v___x_3231_, v_toPure_3232_, v___x_3258_);
return v___x_3259_;
}
else
{
lean_inc_ref(v_type_3242_);
lean_dec_ref(v_newHyp_3241_);
lean_dec(v___x_3231_);
lean_dec(v_snd_3230_);
goto v___jp_3250_;
}
}
v___jp_3250_:
{
lean_object* v_getInheritedTraceOptions_3251_; lean_object* v___x_3252_; lean_object* v___f_3253_; lean_object* v___f_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v_getInheritedTraceOptions_3251_ = lean_ctor_get(v_inst_3235_, 2);
lean_inc(v_getInheritedTraceOptions_3251_);
v___x_3252_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
lean_inc_n(v_toBind_3234_, 3);
v___f_3253_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3253_, 0, v_toPure_3232_);
lean_closure_set(v___f_3253_, 1, v___x_3252_);
lean_closure_set(v___f_3253_, 2, v_toBind_3234_);
lean_closure_set(v___f_3253_, 3, v_inst_3236_);
v___f_3254_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed), 11, 10);
lean_closure_set(v___f_3254_, 0, v___f_3248_);
lean_closure_set(v___f_3254_, 1, v_inst_3237_);
lean_closure_set(v___f_3254_, 2, v___x_3229_);
lean_closure_set(v___f_3254_, 3, v_type_3242_);
lean_closure_set(v___f_3254_, 4, v_inst_3238_);
lean_closure_set(v___f_3254_, 5, v_inst_3235_);
lean_closure_set(v___f_3254_, 6, v_inst_3239_);
lean_closure_set(v___f_3254_, 7, v___x_3252_);
lean_closure_set(v___f_3254_, 8, v_toBind_3234_);
lean_closure_set(v___f_3254_, 9, v___f_3249_);
v___x_3255_ = lean_apply_4(v_toBind_3234_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3251_, v___f_3253_);
v___x_3256_ = lean_apply_4(v_toBind_3234_, lean_box(0), lean_box(0), v___x_3255_, v___f_3254_);
return v___x_3256_;
}
}
else
{
lean_object* v___x_3260_; lean_object* v___f_3261_; lean_object* v___f_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_inc_ref(v_value_3243_);
lean_dec_ref(v_newHyp_3241_);
lean_dec(v_inst_3239_);
lean_dec_ref(v_inst_3238_);
lean_dec_ref(v_inst_3237_);
lean_dec(v_inst_3236_);
lean_dec_ref(v_inst_3235_);
lean_dec(v___x_3231_);
lean_dec_ref(v___x_3229_);
v___x_3260_ = lean_box(v___x_3244_);
v___f_3261_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 4, 3);
lean_closure_set(v___f_3261_, 0, v___x_3260_);
lean_closure_set(v___f_3261_, 1, v_snd_3230_);
lean_closure_set(v___f_3261_, 2, v_toPure_3232_);
lean_inc(v_toBind_3234_);
v___f_3262_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10), 5, 4);
lean_closure_set(v___f_3262_, 0, v_inst_3240_);
lean_closure_set(v___f_3262_, 1, v_value_3243_);
lean_closure_set(v___f_3262_, 2, v_toBind_3234_);
lean_closure_set(v___f_3262_, 3, v___f_3261_);
v___x_3263_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___boxed), 9, 0);
v___x_3264_ = lean_apply_2(v_inst_3233_, lean_box(0), v___x_3263_);
v___x_3265_ = lean_apply_4(v_toBind_3234_, lean_box(0), lean_box(0), v___x_3264_, v___f_3262_);
return v___x_3265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(lean_object* v___x_3266_, lean_object* v_toPure_3267_, lean_object* v_hyps_3268_, lean_object* v___x_3269_, lean_object* v_inst_3270_, lean_object* v_toBind_3271_, lean_object* v_inst_3272_, lean_object* v_inst_3273_, lean_object* v_inst_3274_, lean_object* v_inst_3275_, lean_object* v_inst_3276_, lean_object* v_inst_3277_, lean_object* v_f_3278_, lean_object* v___f_3279_, lean_object* v_next_3280_, lean_object* v_acc_3281_, lean_object* v_h_3282_, lean_object* v_G_3283_){
_start:
{
uint8_t v___x_3284_; 
v___x_3284_ = lean_nat_dec_lt(v_next_3280_, v___x_3266_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; 
lean_dec(v_G_3283_);
lean_dec(v_next_3280_);
lean_dec(v___f_3279_);
lean_dec(v_f_3278_);
lean_dec_ref(v_inst_3277_);
lean_dec(v_inst_3276_);
lean_dec_ref(v_inst_3275_);
lean_dec_ref(v_inst_3274_);
lean_dec(v_inst_3273_);
lean_dec_ref(v_inst_3272_);
lean_dec(v_toBind_3271_);
lean_dec(v_inst_3270_);
lean_dec(v___x_3269_);
v___x_3285_ = lean_apply_2(v_toPure_3267_, lean_box(0), v_acc_3281_);
return v___x_3285_;
}
else
{
lean_object* v_snd_3286_; lean_object* v___f_3287_; lean_object* v___x_3288_; lean_object* v___f_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_snd_3286_ = lean_ctor_get(v_acc_3281_, 1);
lean_inc(v_snd_3286_);
lean_dec_ref(v_acc_3281_);
lean_inc(v_next_3280_);
lean_inc(v_toPure_3267_);
v___f_3287_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3287_, 0, v_toPure_3267_);
lean_closure_set(v___f_3287_, 1, v_next_3280_);
lean_closure_set(v___f_3287_, 2, v_G_3283_);
v___x_3288_ = lean_array_fget_borrowed(v_hyps_3268_, v_next_3280_);
lean_inc_n(v_toBind_3271_, 3);
lean_inc_n(v___x_3288_, 2);
v___f_3289_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__11), 13, 12);
lean_closure_set(v___f_3289_, 0, v___x_3288_);
lean_closure_set(v___f_3289_, 1, v_snd_3286_);
lean_closure_set(v___f_3289_, 2, v___x_3269_);
lean_closure_set(v___f_3289_, 3, v_toPure_3267_);
lean_closure_set(v___f_3289_, 4, v_inst_3270_);
lean_closure_set(v___f_3289_, 5, v_toBind_3271_);
lean_closure_set(v___f_3289_, 6, v_inst_3272_);
lean_closure_set(v___f_3289_, 7, v_inst_3273_);
lean_closure_set(v___f_3289_, 8, v_inst_3274_);
lean_closure_set(v___f_3289_, 9, v_inst_3275_);
lean_closure_set(v___f_3289_, 10, v_inst_3276_);
lean_closure_set(v___f_3289_, 11, v_inst_3277_);
v___x_3290_ = lean_apply_2(v_f_3278_, v_next_3280_, v___x_3288_);
v___x_3291_ = lean_apply_4(v_toBind_3271_, lean_box(0), lean_box(0), v___x_3290_, v___f_3289_);
v___x_3292_ = lean_apply_4(v_toBind_3271_, lean_box(0), lean_box(0), v___x_3291_, v___f_3279_);
v___x_3293_ = lean_apply_4(v_toBind_3271_, lean_box(0), lean_box(0), v___x_3292_, v___f_3287_);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12___boxed(lean_object** _args){
lean_object* v___x_3294_ = _args[0];
lean_object* v_toPure_3295_ = _args[1];
lean_object* v_hyps_3296_ = _args[2];
lean_object* v___x_3297_ = _args[3];
lean_object* v_inst_3298_ = _args[4];
lean_object* v_toBind_3299_ = _args[5];
lean_object* v_inst_3300_ = _args[6];
lean_object* v_inst_3301_ = _args[7];
lean_object* v_inst_3302_ = _args[8];
lean_object* v_inst_3303_ = _args[9];
lean_object* v_inst_3304_ = _args[10];
lean_object* v_inst_3305_ = _args[11];
lean_object* v_f_3306_ = _args[12];
lean_object* v___f_3307_ = _args[13];
lean_object* v_next_3308_ = _args[14];
lean_object* v_acc_3309_ = _args[15];
lean_object* v_h_3310_ = _args[16];
lean_object* v_G_3311_ = _args[17];
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12(v___x_3294_, v_toPure_3295_, v_hyps_3296_, v___x_3297_, v_inst_3298_, v_toBind_3299_, v_inst_3300_, v_inst_3301_, v_inst_3302_, v_inst_3303_, v_inst_3304_, v_inst_3305_, v_f_3306_, v___f_3307_, v_next_3308_, v_acc_3309_, v_h_3310_, v_G_3311_);
lean_dec_ref(v_hyps_3296_);
lean_dec(v___x_3294_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__13(lean_object* v_toPure_3313_, lean_object* v_inst_3314_, lean_object* v_toBind_3315_, lean_object* v_inst_3316_, lean_object* v_inst_3317_, lean_object* v_inst_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_f_3322_, lean_object* v___f_3323_, lean_object* v___f_3324_, lean_object* v_hyps_3325_){
_start:
{
lean_object* v___x_3326_; lean_object* v_newHyps_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___f_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3326_ = lean_array_get_size(v_hyps_3325_);
v_newHyps_3327_ = lean_mk_empty_array_with_capacity(v___x_3326_);
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = lean_box(0);
lean_inc(v_toBind_3315_);
v___f_3330_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__12___boxed), 18, 14);
lean_closure_set(v___f_3330_, 0, v___x_3326_);
lean_closure_set(v___f_3330_, 1, v_toPure_3313_);
lean_closure_set(v___f_3330_, 2, v_hyps_3325_);
lean_closure_set(v___f_3330_, 3, v___x_3329_);
lean_closure_set(v___f_3330_, 4, v_inst_3314_);
lean_closure_set(v___f_3330_, 5, v_toBind_3315_);
lean_closure_set(v___f_3330_, 6, v_inst_3316_);
lean_closure_set(v___f_3330_, 7, v_inst_3317_);
lean_closure_set(v___f_3330_, 8, v_inst_3318_);
lean_closure_set(v___f_3330_, 9, v_inst_3319_);
lean_closure_set(v___f_3330_, 10, v_inst_3320_);
lean_closure_set(v___f_3330_, 11, v_inst_3321_);
lean_closure_set(v___f_3330_, 12, v_f_3322_);
lean_closure_set(v___f_3330_, 13, v___f_3323_);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3329_);
lean_ctor_set(v___x_3331_, 1, v_newHyps_3327_);
v___x_3332_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3330_, v___x_3328_, v___x_3331_, lean_box(0));
v___x_3333_ = lean_apply_4(v_toBind_3315_, lean_box(0), lean_box(0), v___x_3332_, v___f_3324_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg(lean_object* v_inst_3334_, lean_object* v_inst_3335_, lean_object* v_inst_3336_, lean_object* v_inst_3337_, lean_object* v_inst_3338_, lean_object* v_inst_3339_, lean_object* v_inst_3340_, lean_object* v_f_3341_){
_start:
{
lean_object* v_toApplicative_3342_; lean_object* v_toBind_3343_; lean_object* v_toPure_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___f_3347_; lean_object* v___f_3348_; lean_object* v___f_3349_; lean_object* v___f_3350_; lean_object* v___x_3351_; 
v_toApplicative_3342_ = lean_ctor_get(v_inst_3334_, 0);
v_toBind_3343_ = lean_ctor_get(v_inst_3334_, 1);
lean_inc_n(v_toBind_3343_, 3);
v_toPure_3344_ = lean_ctor_get(v_toApplicative_3342_, 1);
lean_inc_n(v_toPure_3344_, 4);
v___x_3345_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
lean_inc_n(v_inst_3335_, 2);
v___x_3346_ = lean_apply_2(v_inst_3335_, lean_box(0), v___x_3345_);
v___f_3347_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3347_, 0, v_toPure_3344_);
v___f_3348_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3348_, 0, v_toPure_3344_);
v___f_3349_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3349_, 0, v_inst_3335_);
lean_closure_set(v___f_3349_, 1, v_toBind_3343_);
lean_closure_set(v___f_3349_, 2, v___f_3348_);
lean_closure_set(v___f_3349_, 3, v_toPure_3344_);
v___f_3350_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3350_, 0, v_toPure_3344_);
lean_closure_set(v___f_3350_, 1, v_inst_3335_);
lean_closure_set(v___f_3350_, 2, v_toBind_3343_);
lean_closure_set(v___f_3350_, 3, v_inst_3338_);
lean_closure_set(v___f_3350_, 4, v_inst_3339_);
lean_closure_set(v___f_3350_, 5, v_inst_3336_);
lean_closure_set(v___f_3350_, 6, v_inst_3334_);
lean_closure_set(v___f_3350_, 7, v_inst_3340_);
lean_closure_set(v___f_3350_, 8, v_inst_3337_);
lean_closure_set(v___f_3350_, 9, v_f_3341_);
lean_closure_set(v___f_3350_, 10, v___f_3347_);
lean_closure_set(v___f_3350_, 11, v___f_3349_);
v___x_3351_ = lean_apply_4(v_toBind_3343_, lean_box(0), lean_box(0), v___x_3346_, v___f_3350_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(lean_object* v_m_3352_, lean_object* v_inst_3353_, lean_object* v_inst_3354_, lean_object* v_inst_3355_, lean_object* v_inst_3356_, lean_object* v_inst_3357_, lean_object* v_inst_3358_, lean_object* v_inst_3359_, lean_object* v_inst_3360_, lean_object* v_f_3361_){
_start:
{
lean_object* v_toApplicative_3362_; lean_object* v_toBind_3363_; lean_object* v_toPure_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___f_3367_; lean_object* v___f_3368_; lean_object* v___f_3369_; lean_object* v___f_3370_; lean_object* v___x_3371_; 
v_toApplicative_3362_ = lean_ctor_get(v_inst_3353_, 0);
v_toBind_3363_ = lean_ctor_get(v_inst_3353_, 1);
lean_inc_n(v_toBind_3363_, 3);
v_toPure_3364_ = lean_ctor_get(v_toApplicative_3362_, 1);
lean_inc_n(v_toPure_3364_, 4);
v___x_3365_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
lean_inc_n(v_inst_3354_, 2);
v___x_3366_ = lean_apply_2(v_inst_3354_, lean_box(0), v___x_3365_);
v___f_3367_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3367_, 0, v_toPure_3364_);
v___f_3368_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3368_, 0, v_toPure_3364_);
v___f_3369_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3369_, 0, v_inst_3354_);
lean_closure_set(v___f_3369_, 1, v_toBind_3363_);
lean_closure_set(v___f_3369_, 2, v___f_3368_);
lean_closure_set(v___f_3369_, 3, v_toPure_3364_);
v___f_3370_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__13), 13, 12);
lean_closure_set(v___f_3370_, 0, v_toPure_3364_);
lean_closure_set(v___f_3370_, 1, v_inst_3354_);
lean_closure_set(v___f_3370_, 2, v_toBind_3363_);
lean_closure_set(v___f_3370_, 3, v_inst_3357_);
lean_closure_set(v___f_3370_, 4, v_inst_3358_);
lean_closure_set(v___f_3370_, 5, v_inst_3355_);
lean_closure_set(v___f_3370_, 6, v_inst_3353_);
lean_closure_set(v___f_3370_, 7, v_inst_3359_);
lean_closure_set(v___f_3370_, 8, v_inst_3356_);
lean_closure_set(v___f_3370_, 9, v_f_3361_);
lean_closure_set(v___f_3370_, 10, v___f_3367_);
lean_closure_set(v___f_3370_, 11, v___f_3369_);
v___x_3371_ = lean_apply_4(v_toBind_3363_, lean_box(0), lean_box(0), v___x_3366_, v___f_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___boxed(lean_object* v_m_3372_, lean_object* v_inst_3373_, lean_object* v_inst_3374_, lean_object* v_inst_3375_, lean_object* v_inst_3376_, lean_object* v_inst_3377_, lean_object* v_inst_3378_, lean_object* v_inst_3379_, lean_object* v_inst_3380_, lean_object* v_f_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps(v_m_3372_, v_inst_3373_, v_inst_3374_, v_inst_3375_, v_inst_3376_, v_inst_3377_, v_inst_3378_, v_inst_3379_, v_inst_3380_, v_f_3381_);
lean_dec_ref(v_inst_3380_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__14(lean_object* v___x_3383_, lean_object* v_snd_3384_, lean_object* v___x_3385_, lean_object* v_toPure_3386_, lean_object* v_inst_3387_, lean_object* v_toBind_3388_, lean_object* v_inst_3389_, lean_object* v_inst_3390_, lean_object* v_inst_3391_, lean_object* v_inst_3392_, lean_object* v_inst_3393_, lean_object* v_inst_3394_, lean_object* v_newHyp_3395_){
_start:
{
lean_object* v_type_3396_; lean_object* v_value_3397_; uint8_t v___x_3398_; 
v_type_3396_ = lean_ctor_get(v_newHyp_3395_, 1);
v_value_3397_ = lean_ctor_get(v_newHyp_3395_, 2);
lean_inc_ref(v_type_3396_);
v___x_3398_ = l_Lean_Expr_isFalse(v_type_3396_);
if (v___x_3398_ == 0)
{
lean_object* v_type_3399_; lean_object* v___f_3400_; lean_object* v___f_3401_; lean_object* v___f_3402_; lean_object* v___f_3403_; uint8_t v___x_3411_; 
lean_dec_ref(v_inst_3394_);
v_type_3399_ = lean_ctor_get(v___x_3383_, 1);
lean_inc(v_toPure_3386_);
lean_inc(v___x_3385_);
lean_inc_ref(v_newHyp_3395_);
lean_inc(v_snd_3384_);
v___f_3400_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5), 5, 4);
lean_closure_set(v___f_3400_, 0, v_snd_3384_);
lean_closure_set(v___f_3400_, 1, v_newHyp_3395_);
lean_closure_set(v___f_3400_, 2, v___x_3385_);
lean_closure_set(v___f_3400_, 3, v_toPure_3386_);
v___f_3401_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3401_, 0, v___f_3400_);
lean_inc(v_toBind_3388_);
v___f_3402_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__7), 4, 3);
lean_closure_set(v___f_3402_, 0, v_inst_3387_);
lean_closure_set(v___f_3402_, 1, v_toBind_3388_);
lean_closure_set(v___f_3402_, 2, v___f_3401_);
lean_inc_ref(v___f_3402_);
v___f_3403_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__10), 2, 1);
lean_closure_set(v___f_3403_, 0, v___f_3402_);
v___x_3411_ = lean_expr_eqv(v_type_3399_, v_type_3396_);
if (v___x_3411_ == 0)
{
lean_inc_ref(v_type_3396_);
lean_dec_ref(v_newHyp_3395_);
lean_dec(v___x_3385_);
lean_dec(v_snd_3384_);
goto v___jp_3404_;
}
else
{
if (v___x_3398_ == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_dec_ref(v___f_3403_);
lean_dec_ref(v___f_3402_);
lean_dec(v_inst_3393_);
lean_dec(v_inst_3392_);
lean_dec_ref(v_inst_3391_);
lean_dec_ref(v_inst_3390_);
lean_dec_ref(v_inst_3389_);
lean_dec(v_toBind_3388_);
lean_dec_ref(v___x_3383_);
v___x_3412_ = lean_box(0);
v___x_3413_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__5(v_snd_3384_, v_newHyp_3395_, v___x_3385_, v_toPure_3386_, v___x_3412_);
return v___x_3413_;
}
else
{
lean_inc_ref(v_type_3396_);
lean_dec_ref(v_newHyp_3395_);
lean_dec(v___x_3385_);
lean_dec(v_snd_3384_);
goto v___jp_3404_;
}
}
v___jp_3404_:
{
lean_object* v_getInheritedTraceOptions_3405_; lean_object* v___x_3406_; lean_object* v___f_3407_; lean_object* v___f_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v_getInheritedTraceOptions_3405_ = lean_ctor_get(v_inst_3389_, 2);
lean_inc(v_getInheritedTraceOptions_3405_);
v___x_3406_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
lean_inc_n(v_toBind_3388_, 3);
v___f_3407_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__7___boxed), 11, 10);
lean_closure_set(v___f_3407_, 0, v___f_3402_);
lean_closure_set(v___f_3407_, 1, v_inst_3390_);
lean_closure_set(v___f_3407_, 2, v___x_3383_);
lean_closure_set(v___f_3407_, 3, v_type_3396_);
lean_closure_set(v___f_3407_, 4, v_inst_3391_);
lean_closure_set(v___f_3407_, 5, v_inst_3389_);
lean_closure_set(v___f_3407_, 6, v_inst_3392_);
lean_closure_set(v___f_3407_, 7, v___x_3406_);
lean_closure_set(v___f_3407_, 8, v_toBind_3388_);
lean_closure_set(v___f_3407_, 9, v___f_3403_);
v___f_3408_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__6), 5, 4);
lean_closure_set(v___f_3408_, 0, v_toPure_3386_);
lean_closure_set(v___f_3408_, 1, v___x_3406_);
lean_closure_set(v___f_3408_, 2, v_toBind_3388_);
lean_closure_set(v___f_3408_, 3, v_inst_3393_);
v___x_3409_ = lean_apply_4(v_toBind_3388_, lean_box(0), lean_box(0), v_getInheritedTraceOptions_3405_, v___f_3408_);
v___x_3410_ = lean_apply_4(v_toBind_3388_, lean_box(0), lean_box(0), v___x_3409_, v___f_3407_);
return v___x_3410_;
}
}
else
{
lean_object* v___x_3414_; lean_object* v___f_3415_; lean_object* v___f_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_inc_ref(v_value_3397_);
lean_dec_ref(v_newHyp_3395_);
lean_dec(v_inst_3393_);
lean_dec(v_inst_3392_);
lean_dec_ref(v_inst_3391_);
lean_dec_ref(v_inst_3390_);
lean_dec_ref(v_inst_3389_);
lean_dec(v___x_3385_);
lean_dec_ref(v___x_3383_);
v___x_3414_ = lean_box(v___x_3398_);
v___f_3415_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__8___boxed), 4, 3);
lean_closure_set(v___f_3415_, 0, v___x_3414_);
lean_closure_set(v___f_3415_, 1, v_snd_3384_);
lean_closure_set(v___f_3415_, 2, v_toPure_3386_);
lean_inc(v_toBind_3388_);
v___f_3416_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__10), 5, 4);
lean_closure_set(v___f_3416_, 0, v_inst_3394_);
lean_closure_set(v___f_3416_, 1, v_value_3397_);
lean_closure_set(v___f_3416_, 2, v_toBind_3388_);
lean_closure_set(v___f_3416_, 3, v___f_3415_);
v___x_3417_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getGoal___boxed), 9, 0);
v___x_3418_ = lean_apply_2(v_inst_3387_, lean_box(0), v___x_3417_);
v___x_3419_ = lean_apply_4(v_toBind_3388_, lean_box(0), lean_box(0), v___x_3418_, v___f_3416_);
return v___x_3419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(lean_object* v___x_3420_, lean_object* v_toPure_3421_, lean_object* v_hyps_3422_, lean_object* v___x_3423_, lean_object* v_inst_3424_, lean_object* v_toBind_3425_, lean_object* v_inst_3426_, lean_object* v_inst_3427_, lean_object* v_inst_3428_, lean_object* v_inst_3429_, lean_object* v_inst_3430_, lean_object* v_inst_3431_, lean_object* v_f_3432_, lean_object* v___f_3433_, lean_object* v_next_3434_, lean_object* v_acc_3435_, lean_object* v_h_3436_, lean_object* v_G_3437_){
_start:
{
uint8_t v___x_3438_; 
v___x_3438_ = lean_nat_dec_lt(v_next_3434_, v___x_3420_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; 
lean_dec(v_G_3437_);
lean_dec(v_next_3434_);
lean_dec(v___f_3433_);
lean_dec(v_f_3432_);
lean_dec_ref(v_inst_3431_);
lean_dec(v_inst_3430_);
lean_dec(v_inst_3429_);
lean_dec_ref(v_inst_3428_);
lean_dec_ref(v_inst_3427_);
lean_dec_ref(v_inst_3426_);
lean_dec(v_toBind_3425_);
lean_dec(v_inst_3424_);
lean_dec(v___x_3423_);
v___x_3439_ = lean_apply_2(v_toPure_3421_, lean_box(0), v_acc_3435_);
return v___x_3439_;
}
else
{
lean_object* v_snd_3440_; lean_object* v___f_3441_; lean_object* v___x_3442_; lean_object* v___f_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v_snd_3440_ = lean_ctor_get(v_acc_3435_, 1);
lean_inc(v_snd_3440_);
lean_dec_ref(v_acc_3435_);
lean_inc(v_next_3434_);
lean_inc(v_toPure_3421_);
v___f_3441_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_3441_, 0, v_toPure_3421_);
lean_closure_set(v___f_3441_, 1, v_next_3434_);
lean_closure_set(v___f_3441_, 2, v_G_3437_);
v___x_3442_ = lean_array_fget_borrowed(v_hyps_3422_, v_next_3434_);
lean_dec(v_next_3434_);
lean_inc_n(v_toBind_3425_, 3);
lean_inc_n(v___x_3442_, 2);
v___f_3443_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__14), 13, 12);
lean_closure_set(v___f_3443_, 0, v___x_3442_);
lean_closure_set(v___f_3443_, 1, v_snd_3440_);
lean_closure_set(v___f_3443_, 2, v___x_3423_);
lean_closure_set(v___f_3443_, 3, v_toPure_3421_);
lean_closure_set(v___f_3443_, 4, v_inst_3424_);
lean_closure_set(v___f_3443_, 5, v_toBind_3425_);
lean_closure_set(v___f_3443_, 6, v_inst_3426_);
lean_closure_set(v___f_3443_, 7, v_inst_3427_);
lean_closure_set(v___f_3443_, 8, v_inst_3428_);
lean_closure_set(v___f_3443_, 9, v_inst_3429_);
lean_closure_set(v___f_3443_, 10, v_inst_3430_);
lean_closure_set(v___f_3443_, 11, v_inst_3431_);
v___x_3444_ = lean_apply_1(v_f_3432_, v___x_3442_);
v___x_3445_ = lean_apply_4(v_toBind_3425_, lean_box(0), lean_box(0), v___x_3444_, v___f_3443_);
v___x_3446_ = lean_apply_4(v_toBind_3425_, lean_box(0), lean_box(0), v___x_3445_, v___f_3433_);
v___x_3447_ = lean_apply_4(v_toBind_3425_, lean_box(0), lean_box(0), v___x_3446_, v___f_3441_);
return v___x_3447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3448_ = _args[0];
lean_object* v_toPure_3449_ = _args[1];
lean_object* v_hyps_3450_ = _args[2];
lean_object* v___x_3451_ = _args[3];
lean_object* v_inst_3452_ = _args[4];
lean_object* v_toBind_3453_ = _args[5];
lean_object* v_inst_3454_ = _args[6];
lean_object* v_inst_3455_ = _args[7];
lean_object* v_inst_3456_ = _args[8];
lean_object* v_inst_3457_ = _args[9];
lean_object* v_inst_3458_ = _args[10];
lean_object* v_inst_3459_ = _args[11];
lean_object* v_f_3460_ = _args[12];
lean_object* v___f_3461_ = _args[13];
lean_object* v_next_3462_ = _args[14];
lean_object* v_acc_3463_ = _args[15];
lean_object* v_h_3464_ = _args[16];
lean_object* v_G_3465_ = _args[17];
_start:
{
lean_object* v_res_3466_; 
v_res_3466_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0(v___x_3448_, v_toPure_3449_, v_hyps_3450_, v___x_3451_, v_inst_3452_, v_toBind_3453_, v_inst_3454_, v_inst_3455_, v_inst_3456_, v_inst_3457_, v_inst_3458_, v_inst_3459_, v_f_3460_, v___f_3461_, v_next_3462_, v_acc_3463_, v_h_3464_, v_G_3465_);
lean_dec_ref(v_hyps_3450_);
lean_dec(v___x_3448_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1(lean_object* v_toPure_3467_, lean_object* v_inst_3468_, lean_object* v_toBind_3469_, lean_object* v_inst_3470_, lean_object* v_inst_3471_, lean_object* v_inst_3472_, lean_object* v_inst_3473_, lean_object* v_inst_3474_, lean_object* v_inst_3475_, lean_object* v_f_3476_, lean_object* v___f_3477_, lean_object* v___f_3478_, lean_object* v_hyps_3479_){
_start:
{
lean_object* v___x_3480_; lean_object* v_newHyps_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___f_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3480_ = lean_array_get_size(v_hyps_3479_);
v_newHyps_3481_ = lean_mk_empty_array_with_capacity(v___x_3480_);
v___x_3482_ = lean_unsigned_to_nat(0u);
v___x_3483_ = lean_box(0);
lean_inc(v_toBind_3469_);
v___f_3484_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__0___boxed), 18, 14);
lean_closure_set(v___f_3484_, 0, v___x_3480_);
lean_closure_set(v___f_3484_, 1, v_toPure_3467_);
lean_closure_set(v___f_3484_, 2, v_hyps_3479_);
lean_closure_set(v___f_3484_, 3, v___x_3483_);
lean_closure_set(v___f_3484_, 4, v_inst_3468_);
lean_closure_set(v___f_3484_, 5, v_toBind_3469_);
lean_closure_set(v___f_3484_, 6, v_inst_3470_);
lean_closure_set(v___f_3484_, 7, v_inst_3471_);
lean_closure_set(v___f_3484_, 8, v_inst_3472_);
lean_closure_set(v___f_3484_, 9, v_inst_3473_);
lean_closure_set(v___f_3484_, 10, v_inst_3474_);
lean_closure_set(v___f_3484_, 11, v_inst_3475_);
lean_closure_set(v___f_3484_, 12, v_f_3476_);
lean_closure_set(v___f_3484_, 13, v___f_3477_);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3483_);
lean_ctor_set(v___x_3485_, 1, v_newHyps_3481_);
v___x_3486_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3484_, v___x_3482_, v___x_3485_, lean_box(0));
v___x_3487_ = lean_apply_4(v_toBind_3469_, lean_box(0), lean_box(0), v___x_3486_, v___f_3478_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg(lean_object* v_inst_3488_, lean_object* v_inst_3489_, lean_object* v_inst_3490_, lean_object* v_inst_3491_, lean_object* v_inst_3492_, lean_object* v_inst_3493_, lean_object* v_inst_3494_, lean_object* v_f_3495_){
_start:
{
lean_object* v_toApplicative_3496_; lean_object* v_toBind_3497_; lean_object* v_toPure_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___f_3501_; lean_object* v___f_3502_; lean_object* v___f_3503_; lean_object* v___f_3504_; lean_object* v___x_3505_; 
v_toApplicative_3496_ = lean_ctor_get(v_inst_3488_, 0);
v_toBind_3497_ = lean_ctor_get(v_inst_3488_, 1);
lean_inc_n(v_toBind_3497_, 3);
v_toPure_3498_ = lean_ctor_get(v_toApplicative_3496_, 1);
lean_inc_n(v_toPure_3498_, 4);
v___x_3499_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
lean_inc_n(v_inst_3489_, 2);
v___x_3500_ = lean_apply_2(v_inst_3489_, lean_box(0), v___x_3499_);
v___f_3501_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3501_, 0, v_toPure_3498_);
v___f_3502_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3502_, 0, v_inst_3489_);
lean_closure_set(v___f_3502_, 1, v_toBind_3497_);
lean_closure_set(v___f_3502_, 2, v___f_3501_);
lean_closure_set(v___f_3502_, 3, v_toPure_3498_);
v___f_3503_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3503_, 0, v_toPure_3498_);
v___f_3504_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 13, 12);
lean_closure_set(v___f_3504_, 0, v_toPure_3498_);
lean_closure_set(v___f_3504_, 1, v_inst_3489_);
lean_closure_set(v___f_3504_, 2, v_toBind_3497_);
lean_closure_set(v___f_3504_, 3, v_inst_3492_);
lean_closure_set(v___f_3504_, 4, v_inst_3490_);
lean_closure_set(v___f_3504_, 5, v_inst_3488_);
lean_closure_set(v___f_3504_, 6, v_inst_3494_);
lean_closure_set(v___f_3504_, 7, v_inst_3493_);
lean_closure_set(v___f_3504_, 8, v_inst_3491_);
lean_closure_set(v___f_3504_, 9, v_f_3495_);
lean_closure_set(v___f_3504_, 10, v___f_3503_);
lean_closure_set(v___f_3504_, 11, v___f_3502_);
v___x_3505_ = lean_apply_4(v_toBind_3497_, lean_box(0), lean_box(0), v___x_3500_, v___f_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(lean_object* v_m_3506_, lean_object* v_inst_3507_, lean_object* v_inst_3508_, lean_object* v_inst_3509_, lean_object* v_inst_3510_, lean_object* v_inst_3511_, lean_object* v_inst_3512_, lean_object* v_inst_3513_, lean_object* v_inst_3514_, lean_object* v_f_3515_){
_start:
{
lean_object* v_toApplicative_3516_; lean_object* v_toBind_3517_; lean_object* v_toPure_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___f_3521_; lean_object* v___f_3522_; lean_object* v___f_3523_; lean_object* v___f_3524_; lean_object* v___x_3525_; 
v_toApplicative_3516_ = lean_ctor_get(v_inst_3507_, 0);
v_toBind_3517_ = lean_ctor_get(v_inst_3507_, 1);
lean_inc_n(v_toBind_3517_, 3);
v_toPure_3518_ = lean_ctor_get(v_toApplicative_3516_, 1);
lean_inc_n(v_toPure_3518_, 4);
v___x_3519_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
lean_inc_n(v_inst_3508_, 2);
v___x_3520_ = lean_apply_2(v_inst_3508_, lean_box(0), v___x_3519_);
v___f_3521_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3521_, 0, v_toPure_3518_);
v___f_3522_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__3), 5, 4);
lean_closure_set(v___f_3522_, 0, v_inst_3508_);
lean_closure_set(v___f_3522_, 1, v_toBind_3517_);
lean_closure_set(v___f_3522_, 2, v___f_3521_);
lean_closure_set(v___f_3522_, 3, v_toPure_3518_);
v___f_3523_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapIdxHyps___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3523_, 0, v_toPure_3518_);
v___f_3524_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___redArg___lam__1), 13, 12);
lean_closure_set(v___f_3524_, 0, v_toPure_3518_);
lean_closure_set(v___f_3524_, 1, v_inst_3508_);
lean_closure_set(v___f_3524_, 2, v_toBind_3517_);
lean_closure_set(v___f_3524_, 3, v_inst_3511_);
lean_closure_set(v___f_3524_, 4, v_inst_3509_);
lean_closure_set(v___f_3524_, 5, v_inst_3507_);
lean_closure_set(v___f_3524_, 6, v_inst_3513_);
lean_closure_set(v___f_3524_, 7, v_inst_3512_);
lean_closure_set(v___f_3524_, 8, v_inst_3510_);
lean_closure_set(v___f_3524_, 9, v_f_3515_);
lean_closure_set(v___f_3524_, 10, v___f_3523_);
lean_closure_set(v___f_3524_, 11, v___f_3522_);
v___x_3525_ = lean_apply_4(v_toBind_3517_, lean_box(0), lean_box(0), v___x_3520_, v___f_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps___boxed(lean_object* v_m_3526_, lean_object* v_inst_3527_, lean_object* v_inst_3528_, lean_object* v_inst_3529_, lean_object* v_inst_3530_, lean_object* v_inst_3531_, lean_object* v_inst_3532_, lean_object* v_inst_3533_, lean_object* v_inst_3534_, lean_object* v_f_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapHyps(v_m_3526_, v_inst_3527_, v_inst_3528_, v_inst_3529_, v_inst_3530_, v_inst_3531_, v_inst_3532_, v_inst_3533_, v_inst_3534_, v_f_3535_);
lean_dec_ref(v_inst_3534_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0(lean_object* v_f_3537_, lean_object* v_x_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = lean_apply_1(v_f_3537_, v___y_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1(lean_object* v_toApplicative_3541_, lean_object* v_inst_3542_, lean_object* v___f_3543_, lean_object* v_hyps_3544_){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v___x_3545_ = lean_unsigned_to_nat(0u);
v___x_3546_ = lean_array_get_size(v_hyps_3544_);
v___x_3547_ = lean_box(0);
v___x_3548_ = lean_nat_dec_lt(v___x_3545_, v___x_3546_);
if (v___x_3548_ == 0)
{
lean_object* v_toPure_3549_; lean_object* v___x_3550_; 
lean_dec_ref(v_hyps_3544_);
lean_dec(v___f_3543_);
lean_dec_ref(v_inst_3542_);
v_toPure_3549_ = lean_ctor_get(v_toApplicative_3541_, 1);
lean_inc(v_toPure_3549_);
lean_dec_ref(v_toApplicative_3541_);
v___x_3550_ = lean_apply_2(v_toPure_3549_, lean_box(0), v___x_3547_);
return v___x_3550_;
}
else
{
uint8_t v___x_3551_; 
v___x_3551_ = lean_nat_dec_le(v___x_3546_, v___x_3546_);
if (v___x_3551_ == 0)
{
if (v___x_3548_ == 0)
{
lean_object* v_toPure_3552_; lean_object* v___x_3553_; 
lean_dec_ref(v_hyps_3544_);
lean_dec(v___f_3543_);
lean_dec_ref(v_inst_3542_);
v_toPure_3552_ = lean_ctor_get(v_toApplicative_3541_, 1);
lean_inc(v_toPure_3552_);
lean_dec_ref(v_toApplicative_3541_);
v___x_3553_ = lean_apply_2(v_toPure_3552_, lean_box(0), v___x_3547_);
return v___x_3553_;
}
else
{
size_t v___x_3554_; size_t v___x_3555_; lean_object* v___x_3556_; 
lean_dec_ref(v_toApplicative_3541_);
v___x_3554_ = ((size_t)0ULL);
v___x_3555_ = lean_usize_of_nat(v___x_3546_);
v___x_3556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3542_, v___f_3543_, v_hyps_3544_, v___x_3554_, v___x_3555_, v___x_3547_);
return v___x_3556_;
}
}
else
{
size_t v___x_3557_; size_t v___x_3558_; lean_object* v___x_3559_; 
lean_dec_ref(v_toApplicative_3541_);
v___x_3557_ = ((size_t)0ULL);
v___x_3558_ = lean_usize_of_nat(v___x_3546_);
v___x_3559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_3542_, v___f_3543_, v_hyps_3544_, v___x_3557_, v___x_3558_, v___x_3547_);
return v___x_3559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg(lean_object* v_inst_3560_, lean_object* v_inst_3561_, lean_object* v_f_3562_){
_start:
{
lean_object* v_toApplicative_3563_; lean_object* v_toBind_3564_; lean_object* v___f_3565_; lean_object* v___f_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_toApplicative_3563_ = lean_ctor_get(v_inst_3560_, 0);
lean_inc_ref(v_toApplicative_3563_);
v_toBind_3564_ = lean_ctor_get(v_inst_3560_, 1);
lean_inc(v_toBind_3564_);
v___f_3565_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3565_, 0, v_f_3562_);
v___f_3566_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3566_, 0, v_toApplicative_3563_);
lean_closure_set(v___f_3566_, 1, v_inst_3560_);
lean_closure_set(v___f_3566_, 2, v___f_3565_);
v___x_3567_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
v___x_3568_ = lean_apply_2(v_inst_3561_, lean_box(0), v___x_3567_);
v___x_3569_ = lean_apply_4(v_toBind_3564_, lean_box(0), lean_box(0), v___x_3568_, v___f_3566_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(lean_object* v_m_3570_, lean_object* v_inst_3571_, lean_object* v_inst_3572_, lean_object* v_inst_3573_, lean_object* v_f_3574_){
_start:
{
lean_object* v_toApplicative_3575_; lean_object* v_toBind_3576_; lean_object* v___f_3577_; lean_object* v___f_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_toApplicative_3575_ = lean_ctor_get(v_inst_3571_, 0);
lean_inc_ref(v_toApplicative_3575_);
v_toBind_3576_ = lean_ctor_get(v_inst_3571_, 1);
lean_inc(v_toBind_3576_);
v___f_3577_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3577_, 0, v_f_3574_);
v___f_3578_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___redArg___lam__1), 4, 3);
lean_closure_set(v___f_3578_, 0, v_toApplicative_3575_);
lean_closure_set(v___f_3578_, 1, v_inst_3571_);
lean_closure_set(v___f_3578_, 2, v___f_3577_);
v___x_3579_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getHyps___boxed), 9, 0);
v___x_3580_ = lean_apply_2(v_inst_3572_, lean_box(0), v___x_3579_);
v___x_3581_ = lean_apply_4(v_toBind_3576_, lean_box(0), lean_box(0), v___x_3580_, v___f_3578_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps___boxed(lean_object* v_m_3582_, lean_object* v_inst_3583_, lean_object* v_inst_3584_, lean_object* v_inst_3585_, lean_object* v_f_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_forHyps(v_m_3582_, v_inst_3583_, v_inst_3584_, v_inst_3585_, v_f_3586_);
lean_dec_ref(v_inst_3585_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(lean_object* v_msgData_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; lean_object* v_env_3595_; lean_object* v___x_3596_; lean_object* v_mctx_3597_; lean_object* v_lctx_3598_; lean_object* v_options_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3594_ = lean_st_ref_get(v___y_3592_);
v_env_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc_ref(v_env_3595_);
lean_dec(v___x_3594_);
v___x_3596_ = lean_st_ref_get(v___y_3590_);
v_mctx_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc_ref(v_mctx_3597_);
lean_dec(v___x_3596_);
v_lctx_3598_ = lean_ctor_get(v___y_3589_, 2);
v_options_3599_ = lean_ctor_get(v___y_3591_, 2);
lean_inc_ref(v_options_3599_);
lean_inc_ref(v_lctx_3598_);
v___x_3600_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3600_, 0, v_env_3595_);
lean_ctor_set(v___x_3600_, 1, v_mctx_3597_);
lean_ctor_set(v___x_3600_, 2, v_lctx_3598_);
lean_ctor_set(v___x_3600_, 3, v_options_3599_);
v___x_3601_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
lean_ctor_set(v___x_3601_, 1, v_msgData_3588_);
v___x_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0___boxed(lean_object* v_msgData_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msgData_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
return v_res_3609_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3610_; double v___x_3611_; 
v___x_3610_ = lean_unsigned_to_nat(0u);
v___x_3611_ = lean_float_of_nat(v___x_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(lean_object* v_cls_3615_, lean_object* v_msg_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v_ref_3622_; lean_object* v___x_3623_; lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3668_; 
v_ref_3622_ = lean_ctor_get(v___y_3619_, 5);
v___x_3623_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3668_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3668_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3628_; lean_object* v_traceState_3629_; lean_object* v_env_3630_; lean_object* v_nextMacroScope_3631_; lean_object* v_ngen_3632_; lean_object* v_auxDeclNGen_3633_; lean_object* v_cache_3634_; lean_object* v_messages_3635_; lean_object* v_infoState_3636_; lean_object* v_snapshotTasks_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3667_; 
v___x_3628_ = lean_st_ref_take(v___y_3620_);
v_traceState_3629_ = lean_ctor_get(v___x_3628_, 4);
v_env_3630_ = lean_ctor_get(v___x_3628_, 0);
v_nextMacroScope_3631_ = lean_ctor_get(v___x_3628_, 1);
v_ngen_3632_ = lean_ctor_get(v___x_3628_, 2);
v_auxDeclNGen_3633_ = lean_ctor_get(v___x_3628_, 3);
v_cache_3634_ = lean_ctor_get(v___x_3628_, 5);
v_messages_3635_ = lean_ctor_get(v___x_3628_, 6);
v_infoState_3636_ = lean_ctor_get(v___x_3628_, 7);
v_snapshotTasks_3637_ = lean_ctor_get(v___x_3628_, 8);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3639_ = v___x_3628_;
v_isShared_3640_ = v_isSharedCheck_3667_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_snapshotTasks_3637_);
lean_inc(v_infoState_3636_);
lean_inc(v_messages_3635_);
lean_inc(v_cache_3634_);
lean_inc(v_traceState_3629_);
lean_inc(v_auxDeclNGen_3633_);
lean_inc(v_ngen_3632_);
lean_inc(v_nextMacroScope_3631_);
lean_inc(v_env_3630_);
lean_dec(v___x_3628_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3667_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
uint64_t v_tid_3641_; lean_object* v_traces_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3666_; 
v_tid_3641_ = lean_ctor_get_uint64(v_traceState_3629_, sizeof(void*)*1);
v_traces_3642_ = lean_ctor_get(v_traceState_3629_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v_traceState_3629_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3644_ = v_traceState_3629_;
v_isShared_3645_ = v_isSharedCheck_3666_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_traces_3642_);
lean_dec(v_traceState_3629_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3666_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3646_; double v___x_3647_; uint8_t v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3646_ = lean_box(0);
v___x_3647_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_3648_ = 0;
v___x_3649_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_3650_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3650_, 0, v_cls_3615_);
lean_ctor_set(v___x_3650_, 1, v___x_3646_);
lean_ctor_set(v___x_3650_, 2, v___x_3649_);
lean_ctor_set_float(v___x_3650_, sizeof(void*)*3, v___x_3647_);
lean_ctor_set_float(v___x_3650_, sizeof(void*)*3 + 8, v___x_3647_);
lean_ctor_set_uint8(v___x_3650_, sizeof(void*)*3 + 16, v___x_3648_);
v___x_3651_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_3652_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3650_);
lean_ctor_set(v___x_3652_, 1, v_a_3624_);
lean_ctor_set(v___x_3652_, 2, v___x_3651_);
lean_inc(v_ref_3622_);
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v_ref_3622_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = l_Lean_PersistentArray_push___redArg(v_traces_3642_, v___x_3653_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3654_);
v___x_3656_ = v___x_3644_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3654_);
lean_ctor_set_uint64(v_reuseFailAlloc_3665_, sizeof(void*)*1, v_tid_3641_);
v___x_3656_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3658_; 
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 4, v___x_3656_);
v___x_3658_ = v___x_3639_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_env_3630_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_nextMacroScope_3631_);
lean_ctor_set(v_reuseFailAlloc_3664_, 2, v_ngen_3632_);
lean_ctor_set(v_reuseFailAlloc_3664_, 3, v_auxDeclNGen_3633_);
lean_ctor_set(v_reuseFailAlloc_3664_, 4, v___x_3656_);
lean_ctor_set(v_reuseFailAlloc_3664_, 5, v_cache_3634_);
lean_ctor_set(v_reuseFailAlloc_3664_, 6, v_messages_3635_);
lean_ctor_set(v_reuseFailAlloc_3664_, 7, v_infoState_3636_);
lean_ctor_set(v_reuseFailAlloc_3664_, 8, v_snapshotTasks_3637_);
v___x_3658_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3662_; 
v___x_3659_ = lean_st_ref_set(v___y_3620_, v___x_3658_);
v___x_3660_ = lean_box(0);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 0, v___x_3660_);
v___x_3662_ = v___x_3626_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3660_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_3669_, lean_object* v_msg_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_3669_, v_msg_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(lean_object* v_x_3677_, lean_object* v_x_3678_, lean_object* v_x_3679_, lean_object* v_x_3680_){
_start:
{
lean_object* v_ks_3681_; lean_object* v_vs_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3706_; 
v_ks_3681_ = lean_ctor_get(v_x_3677_, 0);
v_vs_3682_ = lean_ctor_get(v_x_3677_, 1);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_x_3677_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3684_ = v_x_3677_;
v_isShared_3685_ = v_isSharedCheck_3706_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_vs_3682_);
lean_inc(v_ks_3681_);
lean_dec(v_x_3677_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3706_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; uint8_t v___x_3687_; 
v___x_3686_ = lean_array_get_size(v_ks_3681_);
v___x_3687_ = lean_nat_dec_lt(v_x_3678_, v___x_3686_);
if (v___x_3687_ == 0)
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3691_; 
lean_dec(v_x_3678_);
v___x_3688_ = lean_array_push(v_ks_3681_, v_x_3679_);
v___x_3689_ = lean_array_push(v_vs_3682_, v_x_3680_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 1, v___x_3689_);
lean_ctor_set(v___x_3684_, 0, v___x_3688_);
v___x_3691_ = v___x_3684_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3688_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
else
{
lean_object* v_k_x27_3693_; uint8_t v___x_3694_; 
v_k_x27_3693_ = lean_array_fget_borrowed(v_ks_3681_, v_x_3678_);
v___x_3694_ = l_Lean_instBEqMVarId_beq(v_x_3679_, v_k_x27_3693_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3696_; 
if (v_isShared_3685_ == 0)
{
v___x_3696_ = v___x_3684_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_ks_3681_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_vs_3682_);
v___x_3696_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = lean_unsigned_to_nat(1u);
v___x_3698_ = lean_nat_add(v_x_3678_, v___x_3697_);
lean_dec(v_x_3678_);
v_x_3677_ = v___x_3696_;
v_x_3678_ = v___x_3698_;
goto _start;
}
}
else
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
v___x_3701_ = lean_array_fset(v_ks_3681_, v_x_3678_, v_x_3679_);
v___x_3702_ = lean_array_fset(v_vs_3682_, v_x_3678_, v_x_3680_);
lean_dec(v_x_3678_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 1, v___x_3702_);
lean_ctor_set(v___x_3684_, 0, v___x_3701_);
v___x_3704_ = v___x_3684_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3701_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v___x_3702_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_n_3707_, lean_object* v_k_3708_, lean_object* v_v_3709_){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = lean_unsigned_to_nat(0u);
v___x_3711_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_n_3707_, v___x_3710_, v_k_3708_, v_v_3709_);
return v___x_3711_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_3712_; 
v___x_3712_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3713_, size_t v_x_3714_, size_t v_x_3715_, lean_object* v_x_3716_, lean_object* v_x_3717_){
_start:
{
if (lean_obj_tag(v_x_3713_) == 0)
{
lean_object* v_es_3718_; size_t v___x_3719_; size_t v___x_3720_; lean_object* v_j_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v_es_3718_ = lean_ctor_get(v_x_3713_, 0);
v___x_3719_ = ((size_t)31ULL);
v___x_3720_ = lean_usize_land(v_x_3714_, v___x_3719_);
v_j_3721_ = lean_usize_to_nat(v___x_3720_);
v___x_3722_ = lean_array_get_size(v_es_3718_);
v___x_3723_ = lean_nat_dec_lt(v_j_3721_, v___x_3722_);
if (v___x_3723_ == 0)
{
lean_dec(v_j_3721_);
lean_dec(v_x_3717_);
lean_dec(v_x_3716_);
return v_x_3713_;
}
else
{
lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3762_; 
lean_inc_ref(v_es_3718_);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_x_3713_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; 
v_unused_3763_ = lean_ctor_get(v_x_3713_, 0);
lean_dec(v_unused_3763_);
v___x_3725_ = v_x_3713_;
v_isShared_3726_ = v_isSharedCheck_3762_;
goto v_resetjp_3724_;
}
else
{
lean_dec(v_x_3713_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3762_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v_v_3727_; lean_object* v___x_3728_; lean_object* v_xs_x27_3729_; lean_object* v___y_3731_; 
v_v_3727_ = lean_array_fget(v_es_3718_, v_j_3721_);
v___x_3728_ = lean_box(0);
v_xs_x27_3729_ = lean_array_fset(v_es_3718_, v_j_3721_, v___x_3728_);
switch(lean_obj_tag(v_v_3727_))
{
case 0:
{
lean_object* v_key_3736_; lean_object* v_val_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3747_; 
v_key_3736_ = lean_ctor_get(v_v_3727_, 0);
v_val_3737_ = lean_ctor_get(v_v_3727_, 1);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_v_3727_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3739_ = v_v_3727_;
v_isShared_3740_ = v_isSharedCheck_3747_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_val_3737_);
lean_inc(v_key_3736_);
lean_dec(v_v_3727_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3747_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
uint8_t v___x_3741_; 
v___x_3741_ = l_Lean_instBEqMVarId_beq(v_x_3716_, v_key_3736_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
lean_del_object(v___x_3739_);
v___x_3742_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3736_, v_val_3737_, v_x_3716_, v_x_3717_);
v___x_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
v___y_3731_ = v___x_3743_;
goto v___jp_3730_;
}
else
{
lean_object* v___x_3745_; 
lean_dec(v_val_3737_);
lean_dec(v_key_3736_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 1, v_x_3717_);
lean_ctor_set(v___x_3739_, 0, v_x_3716_);
v___x_3745_ = v___x_3739_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_x_3716_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_x_3717_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
v___y_3731_ = v___x_3745_;
goto v___jp_3730_;
}
}
}
}
case 1:
{
lean_object* v_node_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3760_; 
v_node_3748_ = lean_ctor_get(v_v_3727_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v_v_3727_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3750_ = v_v_3727_;
v_isShared_3751_ = v_isSharedCheck_3760_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_node_3748_);
lean_dec(v_v_3727_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3760_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
size_t v___x_3752_; size_t v___x_3753_; size_t v___x_3754_; size_t v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3758_; 
v___x_3752_ = ((size_t)5ULL);
v___x_3753_ = lean_usize_shift_right(v_x_3714_, v___x_3752_);
v___x_3754_ = ((size_t)1ULL);
v___x_3755_ = lean_usize_add(v_x_3715_, v___x_3754_);
v___x_3756_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_node_3748_, v___x_3753_, v___x_3755_, v_x_3716_, v_x_3717_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v___x_3756_);
v___x_3758_ = v___x_3750_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
v___y_3731_ = v___x_3758_;
goto v___jp_3730_;
}
}
}
default: 
{
lean_object* v___x_3761_; 
v___x_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3761_, 0, v_x_3716_);
lean_ctor_set(v___x_3761_, 1, v_x_3717_);
v___y_3731_ = v___x_3761_;
goto v___jp_3730_;
}
}
v___jp_3730_:
{
lean_object* v___x_3732_; lean_object* v___x_3734_; 
v___x_3732_ = lean_array_fset(v_xs_x27_3729_, v_j_3721_, v___y_3731_);
lean_dec(v_j_3721_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3732_);
v___x_3734_ = v___x_3725_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3732_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
}
else
{
lean_object* v_ks_3764_; lean_object* v_vs_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3785_; 
v_ks_3764_ = lean_ctor_get(v_x_3713_, 0);
v_vs_3765_ = lean_ctor_get(v_x_3713_, 1);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_x_3713_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3767_ = v_x_3713_;
v_isShared_3768_ = v_isSharedCheck_3785_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_vs_3765_);
lean_inc(v_ks_3764_);
lean_dec(v_x_3713_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3785_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_ks_3764_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v_vs_3765_);
v___x_3770_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
lean_object* v_newNode_3771_; uint8_t v___y_3773_; size_t v___x_3779_; uint8_t v___x_3780_; 
v_newNode_3771_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5___redArg(v___x_3770_, v_x_3716_, v_x_3717_);
v___x_3779_ = ((size_t)7ULL);
v___x_3780_ = lean_usize_dec_le(v___x_3779_, v_x_3715_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3781_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3771_);
v___x_3782_ = lean_unsigned_to_nat(4u);
v___x_3783_ = lean_nat_dec_lt(v___x_3781_, v___x_3782_);
lean_dec(v___x_3781_);
v___y_3773_ = v___x_3783_;
goto v___jp_3772_;
}
else
{
v___y_3773_ = v___x_3780_;
goto v___jp_3772_;
}
v___jp_3772_:
{
if (v___y_3773_ == 0)
{
lean_object* v_ks_3774_; lean_object* v_vs_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v_ks_3774_ = lean_ctor_get(v_newNode_3771_, 0);
lean_inc_ref(v_ks_3774_);
v_vs_3775_ = lean_ctor_get(v_newNode_3771_, 1);
lean_inc_ref(v_vs_3775_);
lean_dec_ref(v_newNode_3771_);
v___x_3776_ = lean_unsigned_to_nat(0u);
v___x_3777_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___closed__0);
v___x_3778_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(v_x_3715_, v_ks_3774_, v_vs_3775_, v___x_3776_, v___x_3777_);
lean_dec_ref(v_vs_3775_);
lean_dec_ref(v_ks_3774_);
return v___x_3778_;
}
else
{
return v_newNode_3771_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(size_t v_depth_3786_, lean_object* v_keys_3787_, lean_object* v_vals_3788_, lean_object* v_i_3789_, lean_object* v_entries_3790_){
_start:
{
lean_object* v___x_3791_; uint8_t v___x_3792_; 
v___x_3791_ = lean_array_get_size(v_keys_3787_);
v___x_3792_ = lean_nat_dec_lt(v_i_3789_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_dec(v_i_3789_);
return v_entries_3790_;
}
else
{
lean_object* v_k_3793_; lean_object* v_v_3794_; uint64_t v___x_3795_; size_t v_h_3796_; size_t v___x_3797_; lean_object* v___x_3798_; size_t v___x_3799_; size_t v___x_3800_; size_t v___x_3801_; size_t v_h_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v_k_3793_ = lean_array_fget_borrowed(v_keys_3787_, v_i_3789_);
v_v_3794_ = lean_array_fget_borrowed(v_vals_3788_, v_i_3789_);
v___x_3795_ = l_Lean_instHashableMVarId_hash(v_k_3793_);
v_h_3796_ = lean_uint64_to_usize(v___x_3795_);
v___x_3797_ = ((size_t)5ULL);
v___x_3798_ = lean_unsigned_to_nat(1u);
v___x_3799_ = ((size_t)1ULL);
v___x_3800_ = lean_usize_sub(v_depth_3786_, v___x_3799_);
v___x_3801_ = lean_usize_mul(v___x_3797_, v___x_3800_);
v_h_3802_ = lean_usize_shift_right(v_h_3796_, v___x_3801_);
v___x_3803_ = lean_nat_add(v_i_3789_, v___x_3798_);
lean_dec(v_i_3789_);
lean_inc(v_v_3794_);
lean_inc(v_k_3793_);
v___x_3804_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_entries_3790_, v_h_3802_, v_depth_3786_, v_k_3793_, v_v_3794_);
v_i_3789_ = v___x_3803_;
v_entries_3790_ = v___x_3804_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_3806_, lean_object* v_keys_3807_, lean_object* v_vals_3808_, lean_object* v_i_3809_, lean_object* v_entries_3810_){
_start:
{
size_t v_depth_boxed_3811_; lean_object* v_res_3812_; 
v_depth_boxed_3811_ = lean_unbox_usize(v_depth_3806_);
lean_dec(v_depth_3806_);
v_res_3812_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_boxed_3811_, v_keys_3807_, v_vals_3808_, v_i_3809_, v_entries_3810_);
lean_dec_ref(v_vals_3808_);
lean_dec_ref(v_keys_3807_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_x_3813_, lean_object* v_x_3814_, lean_object* v_x_3815_, lean_object* v_x_3816_, lean_object* v_x_3817_){
_start:
{
size_t v_x_24356__boxed_3818_; size_t v_x_24357__boxed_3819_; lean_object* v_res_3820_; 
v_x_24356__boxed_3818_ = lean_unbox_usize(v_x_3814_);
lean_dec(v_x_3814_);
v_x_24357__boxed_3819_ = lean_unbox_usize(v_x_3815_);
lean_dec(v_x_3815_);
v_res_3820_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_x_3813_, v_x_24356__boxed_3818_, v_x_24357__boxed_3819_, v_x_3816_, v_x_3817_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(lean_object* v_x_3821_, lean_object* v_x_3822_, lean_object* v_x_3823_){
_start:
{
uint64_t v___x_3824_; size_t v___x_3825_; size_t v___x_3826_; lean_object* v___x_3827_; 
v___x_3824_ = l_Lean_instHashableMVarId_hash(v_x_3822_);
v___x_3825_ = lean_uint64_to_usize(v___x_3824_);
v___x_3826_ = ((size_t)1ULL);
v___x_3827_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_x_3821_, v___x_3825_, v___x_3826_, v_x_3822_, v_x_3823_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(lean_object* v_mvarId_3828_, lean_object* v_val_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v___x_3832_; lean_object* v_mctx_3833_; lean_object* v_cache_3834_; lean_object* v_zetaDeltaFVarIds_3835_; lean_object* v_postponed_3836_; lean_object* v_diag_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3865_; 
v___x_3832_ = lean_st_ref_take(v___y_3830_);
v_mctx_3833_ = lean_ctor_get(v___x_3832_, 0);
v_cache_3834_ = lean_ctor_get(v___x_3832_, 1);
v_zetaDeltaFVarIds_3835_ = lean_ctor_get(v___x_3832_, 2);
v_postponed_3836_ = lean_ctor_get(v___x_3832_, 3);
v_diag_3837_ = lean_ctor_get(v___x_3832_, 4);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3839_ = v___x_3832_;
v_isShared_3840_ = v_isSharedCheck_3865_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_diag_3837_);
lean_inc(v_postponed_3836_);
lean_inc(v_zetaDeltaFVarIds_3835_);
lean_inc(v_cache_3834_);
lean_inc(v_mctx_3833_);
lean_dec(v___x_3832_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3865_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v_depth_3841_; lean_object* v_levelAssignDepth_3842_; lean_object* v_lmvarCounter_3843_; lean_object* v_mvarCounter_3844_; lean_object* v_lDecls_3845_; lean_object* v_decls_3846_; lean_object* v_userNames_3847_; lean_object* v_lAssignment_3848_; lean_object* v_eAssignment_3849_; lean_object* v_dAssignment_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3864_; 
v_depth_3841_ = lean_ctor_get(v_mctx_3833_, 0);
v_levelAssignDepth_3842_ = lean_ctor_get(v_mctx_3833_, 1);
v_lmvarCounter_3843_ = lean_ctor_get(v_mctx_3833_, 2);
v_mvarCounter_3844_ = lean_ctor_get(v_mctx_3833_, 3);
v_lDecls_3845_ = lean_ctor_get(v_mctx_3833_, 4);
v_decls_3846_ = lean_ctor_get(v_mctx_3833_, 5);
v_userNames_3847_ = lean_ctor_get(v_mctx_3833_, 6);
v_lAssignment_3848_ = lean_ctor_get(v_mctx_3833_, 7);
v_eAssignment_3849_ = lean_ctor_get(v_mctx_3833_, 8);
v_dAssignment_3850_ = lean_ctor_get(v_mctx_3833_, 9);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_mctx_3833_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3852_ = v_mctx_3833_;
v_isShared_3853_ = v_isSharedCheck_3864_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_dAssignment_3850_);
lean_inc(v_eAssignment_3849_);
lean_inc(v_lAssignment_3848_);
lean_inc(v_userNames_3847_);
lean_inc(v_decls_3846_);
lean_inc(v_lDecls_3845_);
lean_inc(v_mvarCounter_3844_);
lean_inc(v_lmvarCounter_3843_);
lean_inc(v_levelAssignDepth_3842_);
lean_inc(v_depth_3841_);
lean_dec(v_mctx_3833_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3864_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3854_; lean_object* v___x_3856_; 
v___x_3854_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(v_eAssignment_3849_, v_mvarId_3828_, v_val_3829_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 8, v___x_3854_);
v___x_3856_ = v___x_3852_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_depth_3841_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_levelAssignDepth_3842_);
lean_ctor_set(v_reuseFailAlloc_3863_, 2, v_lmvarCounter_3843_);
lean_ctor_set(v_reuseFailAlloc_3863_, 3, v_mvarCounter_3844_);
lean_ctor_set(v_reuseFailAlloc_3863_, 4, v_lDecls_3845_);
lean_ctor_set(v_reuseFailAlloc_3863_, 5, v_decls_3846_);
lean_ctor_set(v_reuseFailAlloc_3863_, 6, v_userNames_3847_);
lean_ctor_set(v_reuseFailAlloc_3863_, 7, v_lAssignment_3848_);
lean_ctor_set(v_reuseFailAlloc_3863_, 8, v___x_3854_);
lean_ctor_set(v_reuseFailAlloc_3863_, 9, v_dAssignment_3850_);
v___x_3856_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_object* v___x_3858_; 
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3856_);
v___x_3858_ = v___x_3839_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_cache_3834_);
lean_ctor_set(v_reuseFailAlloc_3862_, 2, v_zetaDeltaFVarIds_3835_);
lean_ctor_set(v_reuseFailAlloc_3862_, 3, v_postponed_3836_);
lean_ctor_set(v_reuseFailAlloc_3862_, 4, v_diag_3837_);
v___x_3858_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = lean_st_ref_set(v___y_3830_, v___x_3858_);
v___x_3860_ = lean_box(0);
v___x_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
return v___x_3861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg___boxed(lean_object* v_mvarId_3866_, lean_object* v_val_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_mvarId_3866_, v_val_3867_, v___y_3868_);
lean_dec(v___y_3868_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(uint8_t v___x_3871_, lean_object* v___f_3872_, lean_object* v_____r_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v___x_3884_; lean_object* v_rewriteSimpCache_3885_; lean_object* v_rewriteDSimpCache_3886_; lean_object* v_acCache_3887_; lean_object* v_typeAnalysis_3888_; lean_object* v_goal_3889_; lean_object* v_hypotheses_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3900_; 
v___x_3884_ = lean_st_ref_take(v___y_3876_);
v_rewriteSimpCache_3885_ = lean_ctor_get(v___x_3884_, 0);
v_rewriteDSimpCache_3886_ = lean_ctor_get(v___x_3884_, 1);
v_acCache_3887_ = lean_ctor_get(v___x_3884_, 2);
v_typeAnalysis_3888_ = lean_ctor_get(v___x_3884_, 3);
v_goal_3889_ = lean_ctor_get(v___x_3884_, 4);
v_hypotheses_3890_ = lean_ctor_get(v___x_3884_, 5);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3892_ = v___x_3884_;
v_isShared_3893_ = v_isSharedCheck_3900_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_hypotheses_3890_);
lean_inc(v_goal_3889_);
lean_inc(v_typeAnalysis_3888_);
lean_inc(v_acCache_3887_);
lean_inc(v_rewriteDSimpCache_3886_);
lean_inc(v_rewriteSimpCache_3885_);
lean_dec(v___x_3884_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3900_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3895_; 
if (v_isShared_3893_ == 0)
{
v___x_3895_ = v___x_3892_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_rewriteSimpCache_3885_);
lean_ctor_set(v_reuseFailAlloc_3899_, 1, v_rewriteDSimpCache_3886_);
lean_ctor_set(v_reuseFailAlloc_3899_, 2, v_acCache_3887_);
lean_ctor_set(v_reuseFailAlloc_3899_, 3, v_typeAnalysis_3888_);
lean_ctor_set(v_reuseFailAlloc_3899_, 4, v_goal_3889_);
lean_ctor_set(v_reuseFailAlloc_3899_, 5, v_hypotheses_3890_);
v___x_3895_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
lean_ctor_set_uint8(v___x_3895_, sizeof(void*)*6, v___x_3871_);
v___x_3896_ = lean_st_ref_set(v___y_3876_, v___x_3895_);
v___x_3897_ = lean_box(0);
lean_inc(v___y_3882_);
lean_inc_ref(v___y_3881_);
lean_inc(v___y_3880_);
lean_inc_ref(v___y_3879_);
lean_inc(v___y_3878_);
lean_inc_ref(v___y_3877_);
lean_inc(v___y_3876_);
lean_inc_ref(v___y_3875_);
lean_inc(v___y_3874_);
v___x_3898_ = lean_apply_11(v___f_3872_, v___x_3897_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, lean_box(0));
return v___x_3898_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1___boxed(lean_object* v___x_3901_, lean_object* v___f_3902_, lean_object* v_____r_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
uint8_t v___x_24569__boxed_3914_; lean_object* v_res_3915_; 
v___x_24569__boxed_3914_ = lean_unbox(v___x_3901_);
v_res_3915_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_24569__boxed_3914_, v___f_3902_, v_____r_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(lean_object* v_snd_3916_, lean_object* v_a_3917_, lean_object* v___x_3918_, lean_object* v_____r_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3930_ = lean_array_push(v_snd_3916_, v_a_3917_);
v___x_3931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3918_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0___boxed(lean_object* v_snd_3934_, lean_object* v_a_3935_, lean_object* v___x_3936_, lean_object* v_____r_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(v_snd_3934_, v_a_3935_, v___x_3936_, v_____r_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(lean_object* v_upperBound_3949_, lean_object* v___x_3950_, lean_object* v_methods_3951_, lean_object* v_config_3952_, lean_object* v_a_3953_, lean_object* v_b_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___y_3966_; uint8_t v___x_3988_; 
v___x_3988_ = lean_nat_dec_lt(v_a_3953_, v_upperBound_3949_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; 
lean_dec(v_a_3953_);
lean_dec_ref(v_config_3952_);
lean_dec_ref(v_methods_3951_);
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v_b_3954_);
return v___x_3989_;
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v_type_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3990_ = lean_st_ref_take(v___y_3955_);
v___x_3991_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_3992_ = lean_st_ref_set(v___y_3955_, v___x_3991_);
v___x_3993_ = lean_array_fget_borrowed(v___x_3950_, v_a_3953_);
v_type_3994_ = lean_ctor_get(v___x_3993_, 1);
v___x_3995_ = lean_unsigned_to_nat(0u);
v___x_3996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
lean_ctor_set(v___x_3996_, 1, v___x_3990_);
lean_ctor_set(v___x_3996_, 2, v___x_3991_);
lean_ctor_set(v___x_3996_, 3, v___x_3991_);
lean_inc_ref(v_type_3994_);
v___x_3997_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3997_, 0, v_type_3994_);
lean_inc_ref(v_config_3952_);
lean_inc_ref(v_methods_3951_);
v___x_3998_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3997_, v_methods_3951_, v_config_3952_, v___x_3996_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v_snd_4000_; lean_object* v_fst_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4083_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v_snd_4000_ = lean_ctor_get(v_a_3999_, 1);
v_fst_4001_ = lean_ctor_get(v_a_3999_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_a_3999_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4003_ = v_a_3999_;
v_isShared_4004_ = v_isSharedCheck_4083_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_snd_4000_);
lean_inc(v_fst_4001_);
lean_dec(v_a_3999_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4083_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v_persistentCache_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v_persistentCache_4005_ = lean_ctor_get(v_snd_4000_, 1);
lean_inc_ref(v_persistentCache_4005_);
lean_dec(v_snd_4000_);
v___x_4006_ = lean_st_ref_set(v___y_3955_, v_persistentCache_4005_);
lean_inc(v___x_3993_);
v___x_4007_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v___x_3993_, v_fst_4001_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v_snd_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4073_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref_known(v___x_4007_, 1);
v_snd_4009_ = lean_ctor_get(v_b_3954_, 1);
v_isSharedCheck_4073_ = !lean_is_exclusive(v_b_3954_);
if (v_isSharedCheck_4073_ == 0)
{
lean_object* v_unused_4074_; 
v_unused_4074_ = lean_ctor_get(v_b_3954_, 0);
lean_dec(v_unused_4074_);
v___x_4011_ = v_b_3954_;
v_isShared_4012_ = v_isSharedCheck_4073_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_snd_4009_);
lean_dec(v_b_3954_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4073_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v_type_4013_; lean_object* v_value_4014_; uint8_t v___x_4015_; 
v_type_4013_ = lean_ctor_get(v_a_4008_, 1);
v_value_4014_ = lean_ctor_get(v_a_4008_, 2);
lean_inc_ref(v_type_4013_);
v___x_4015_ = l_Lean_Expr_isFalse(v_type_4013_);
if (v___x_4015_ == 0)
{
lean_object* v___x_4016_; lean_object* v___f_4017_; uint8_t v___x_4046_; 
lean_del_object(v___x_4011_);
v___x_4016_ = lean_box(0);
lean_inc(v_a_4008_);
lean_inc(v_snd_4009_);
v___f_4017_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0___boxed), 14, 3);
lean_closure_set(v___f_4017_, 0, v_snd_4009_);
lean_closure_set(v___f_4017_, 1, v_a_4008_);
lean_closure_set(v___f_4017_, 2, v___x_4016_);
v___x_4046_ = lean_expr_eqv(v_type_3994_, v_type_4013_);
if (v___x_4046_ == 0)
{
lean_inc_ref(v_type_4013_);
lean_dec(v_snd_4009_);
lean_dec(v_a_4008_);
goto v___jp_4021_;
}
else
{
if (v___x_4015_ == 0)
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
lean_dec_ref(v___f_4017_);
lean_del_object(v___x_4003_);
v___x_4047_ = lean_box(0);
v___x_4048_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(v_snd_4009_, v_a_4008_, v___x_4016_, v___x_4047_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
v___y_3966_ = v___x_4048_;
goto v___jp_3965_;
}
else
{
lean_inc_ref(v_type_4013_);
lean_dec(v_snd_4009_);
lean_dec(v_a_4008_);
goto v___jp_4021_;
}
}
v___jp_4018_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4019_ = lean_box(0);
v___x_4020_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_3988_, v___f_4017_, v___x_4019_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
v___y_3966_ = v___x_4020_;
goto v___jp_3965_;
}
v___jp_4021_:
{
lean_object* v_options_4022_; uint8_t v_hasTrace_4023_; 
v_options_4022_ = lean_ctor_get(v___y_3962_, 2);
v_hasTrace_4023_ = lean_ctor_get_uint8(v_options_4022_, sizeof(void*)*1);
if (v_hasTrace_4023_ == 0)
{
lean_dec_ref(v_type_4013_);
lean_del_object(v___x_4003_);
goto v___jp_4018_;
}
else
{
lean_object* v_inheritedTraceOptions_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; uint8_t v___x_4027_; 
v_inheritedTraceOptions_4024_ = lean_ctor_get(v___y_3962_, 13);
v___x_4025_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_4026_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_4027_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4024_, v_options_4022_, v___x_4026_);
if (v___x_4027_ == 0)
{
lean_dec_ref(v_type_4013_);
lean_del_object(v___x_4003_);
goto v___jp_4018_;
}
else
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4031_; 
lean_inc_ref(v_type_3994_);
v___x_4028_ = l_Lean_MessageData_ofExpr(v_type_3994_);
v___x_4029_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_4004_ == 0)
{
lean_ctor_set_tag(v___x_4003_, 7);
lean_ctor_set(v___x_4003_, 1, v___x_4029_);
lean_ctor_set(v___x_4003_, 0, v___x_4028_);
v___x_4031_ = v___x_4003_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v___x_4029_);
v___x_4031_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4032_ = l_Lean_MessageData_ofExpr(v_type_4013_);
v___x_4033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4031_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
v___x_4034_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v___x_4025_, v___x_4033_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v___x_4036_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
v___x_4036_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_3988_, v___f_4017_, v_a_4035_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
v___y_3966_ = v___x_4036_;
goto v___jp_3965_;
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_dec_ref(v___f_4017_);
lean_dec(v_a_3953_);
lean_dec_ref(v_config_3952_);
lean_dec_ref(v_methods_3951_);
v_a_4037_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4034_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4034_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
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
lean_object* v___x_4049_; lean_object* v_goal_4050_; lean_object* v___x_4051_; 
lean_inc_ref(v_value_4014_);
lean_dec(v_a_4008_);
lean_del_object(v___x_4003_);
lean_dec(v_a_3953_);
lean_dec_ref(v_config_3952_);
lean_dec_ref(v_methods_3951_);
v___x_4049_ = lean_st_ref_get(v___y_3957_);
v_goal_4050_ = lean_ctor_get(v___x_4049_, 4);
lean_inc(v_goal_4050_);
lean_dec(v___x_4049_);
v___x_4051_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_goal_4050_, v_value_4014_, v___y_3961_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4063_; 
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4063_ == 0)
{
lean_object* v_unused_4064_; 
v_unused_4064_ = lean_ctor_get(v___x_4051_, 0);
lean_dec(v_unused_4064_);
v___x_4053_ = v___x_4051_;
v_isShared_4054_ = v_isSharedCheck_4063_;
goto v_resetjp_4052_;
}
else
{
lean_dec(v___x_4051_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4063_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4058_; 
v___x_4055_ = lean_box(v___x_4015_);
v___x_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v___x_4056_);
v___x_4058_ = v___x_4011_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4056_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_snd_4009_);
v___x_4058_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4060_; 
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v___x_4058_);
v___x_4060_ = v___x_4053_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4058_);
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
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_del_object(v___x_4011_);
lean_dec(v_snd_4009_);
v_a_4065_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4051_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4051_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
}
else
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
lean_del_object(v___x_4003_);
lean_dec_ref(v_b_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_config_3952_);
lean_dec_ref(v_methods_3951_);
v_a_4075_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_4007_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4007_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec_ref(v_b_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_config_3952_);
lean_dec_ref(v_methods_3951_);
v_a_4084_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_3998_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_3998_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
v___jp_3965_:
{
if (lean_obj_tag(v___y_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3979_; 
v_a_3967_ = lean_ctor_get(v___y_3966_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___y_3966_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3969_ = v___y_3966_;
v_isShared_3970_ = v_isSharedCheck_3979_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___y_3966_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3979_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
if (lean_obj_tag(v_a_3967_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3973_; 
lean_dec(v_a_3953_);
lean_dec_ref(v_config_3952_);
lean_dec_ref(v_methods_3951_);
v_a_3971_ = lean_ctor_get(v_a_3967_, 0);
lean_inc(v_a_3971_);
lean_dec_ref_known(v_a_3967_, 1);
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v_a_3971_);
v___x_3973_ = v___x_3969_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3971_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
lean_del_object(v___x_3969_);
v_a_3975_ = lean_ctor_get(v_a_3967_, 0);
lean_inc(v_a_3975_);
lean_dec_ref_known(v_a_3967_, 1);
v___x_3976_ = lean_unsigned_to_nat(1u);
v___x_3977_ = lean_nat_add(v_a_3953_, v___x_3976_);
lean_dec(v_a_3953_);
v_a_3953_ = v___x_3977_;
v_b_3954_ = v_a_3975_;
goto _start;
}
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec(v_a_3953_);
lean_dec_ref(v_config_3952_);
lean_dec_ref(v_methods_3951_);
v_a_3980_ = lean_ctor_get(v___y_3966_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___y_3966_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___y_3966_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___y_3966_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___boxed(lean_object* v_upperBound_4092_, lean_object* v___x_4093_, lean_object* v_methods_4094_, lean_object* v_config_4095_, lean_object* v_a_4096_, lean_object* v_b_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(v_upperBound_4092_, v___x_4093_, v_methods_4094_, v_config_4095_, v_a_4096_, v_b_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___x_4093_);
lean_dec(v_upperBound_4092_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(lean_object* v_methods_4109_, lean_object* v_config_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_){
_start:
{
lean_object* v___x_4121_; lean_object* v_hypotheses_4122_; lean_object* v___x_4123_; lean_object* v_newHyps_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4121_ = lean_st_ref_get(v_a_4113_);
v_hypotheses_4122_ = lean_ctor_get(v___x_4121_, 5);
lean_inc_ref(v_hypotheses_4122_);
lean_dec(v___x_4121_);
v___x_4123_ = lean_array_get_size(v_hypotheses_4122_);
v_newHyps_4124_ = lean_mk_empty_array_with_capacity(v___x_4123_);
v___x_4125_ = lean_unsigned_to_nat(0u);
v___x_4126_ = lean_box(0);
v___x_4127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
lean_ctor_set(v___x_4127_, 1, v_newHyps_4124_);
v___x_4128_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(v___x_4123_, v_hypotheses_4122_, v_methods_4109_, v_config_4110_, v___x_4125_, v___x_4127_, v_a_4111_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_);
lean_dec_ref(v_hypotheses_4122_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4160_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4131_ = v___x_4128_;
v_isShared_4132_ = v_isSharedCheck_4160_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4128_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4160_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v_fst_4133_; 
v_fst_4133_ = lean_ctor_get(v_a_4129_, 0);
if (lean_obj_tag(v_fst_4133_) == 0)
{
lean_object* v_snd_4134_; lean_object* v___x_4135_; lean_object* v_rewriteSimpCache_4136_; lean_object* v_rewriteDSimpCache_4137_; lean_object* v_acCache_4138_; lean_object* v_typeAnalysis_4139_; lean_object* v_goal_4140_; uint8_t v_didChange_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4154_; 
v_snd_4134_ = lean_ctor_get(v_a_4129_, 1);
lean_inc(v_snd_4134_);
lean_dec(v_a_4129_);
v___x_4135_ = lean_st_ref_take(v_a_4113_);
v_rewriteSimpCache_4136_ = lean_ctor_get(v___x_4135_, 0);
v_rewriteDSimpCache_4137_ = lean_ctor_get(v___x_4135_, 1);
v_acCache_4138_ = lean_ctor_get(v___x_4135_, 2);
v_typeAnalysis_4139_ = lean_ctor_get(v___x_4135_, 3);
v_goal_4140_ = lean_ctor_get(v___x_4135_, 4);
v_didChange_4141_ = lean_ctor_get_uint8(v___x_4135_, sizeof(void*)*6);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4154_ == 0)
{
lean_object* v_unused_4155_; 
v_unused_4155_ = lean_ctor_get(v___x_4135_, 5);
lean_dec(v_unused_4155_);
v___x_4143_ = v___x_4135_;
v_isShared_4144_ = v_isSharedCheck_4154_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_goal_4140_);
lean_inc(v_typeAnalysis_4139_);
lean_inc(v_acCache_4138_);
lean_inc(v_rewriteDSimpCache_4137_);
lean_inc(v_rewriteSimpCache_4136_);
lean_dec(v___x_4135_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4154_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 5, v_snd_4134_);
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_rewriteSimpCache_4136_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_rewriteDSimpCache_4137_);
lean_ctor_set(v_reuseFailAlloc_4153_, 2, v_acCache_4138_);
lean_ctor_set(v_reuseFailAlloc_4153_, 3, v_typeAnalysis_4139_);
lean_ctor_set(v_reuseFailAlloc_4153_, 4, v_goal_4140_);
lean_ctor_set(v_reuseFailAlloc_4153_, 5, v_snd_4134_);
lean_ctor_set_uint8(v_reuseFailAlloc_4153_, sizeof(void*)*6, v_didChange_4141_);
v___x_4146_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
lean_object* v___x_4147_; uint8_t v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4151_; 
v___x_4147_ = lean_st_ref_set(v_a_4113_, v___x_4146_);
v___x_4148_ = 0;
v___x_4149_ = lean_box(v___x_4148_);
if (v_isShared_4132_ == 0)
{
lean_ctor_set(v___x_4131_, 0, v___x_4149_);
v___x_4151_ = v___x_4131_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4149_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
else
{
lean_object* v_val_4156_; lean_object* v___x_4158_; 
lean_inc_ref(v_fst_4133_);
lean_dec(v_a_4129_);
v_val_4156_ = lean_ctor_get(v_fst_4133_, 0);
lean_inc(v_val_4156_);
lean_dec_ref_known(v_fst_4133_, 1);
if (v_isShared_4132_ == 0)
{
lean_ctor_set(v___x_4131_, 0, v_val_4156_);
v___x_4158_ = v___x_4131_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_val_4156_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
else
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
v_a_4161_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4128_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4128_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go___boxed(lean_object* v_methods_4169_, lean_object* v_config_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_4169_, v_config_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
lean_dec(v_a_4179_);
lean_dec_ref(v_a_4178_);
lean_dec(v_a_4177_);
lean_dec_ref(v_a_4176_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
lean_dec(v_a_4173_);
lean_dec_ref(v_a_4172_);
lean_dec(v_a_4171_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(lean_object* v_cls_4182_, lean_object* v_msg_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg(v_cls_4182_, v_msg_4183_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___boxed(lean_object* v_cls_4195_, lean_object* v_msg_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0(v_cls_4195_, v_msg_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(lean_object* v_mvarId_4208_, lean_object* v_val_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
lean_object* v___x_4220_; 
v___x_4220_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___redArg(v_mvarId_4208_, v_val_4209_, v___y_4216_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1___boxed(lean_object* v_mvarId_4221_, lean_object* v_val_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1(v_mvarId_4221_, v_val_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2(lean_object* v_upperBound_4234_, lean_object* v___x_4235_, lean_object* v_methods_4236_, lean_object* v_config_4237_, lean_object* v_inst_4238_, lean_object* v_R_4239_, lean_object* v_a_4240_, lean_object* v_b_4241_, lean_object* v_c_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg(v_upperBound_4234_, v___x_4235_, v_methods_4236_, v_config_4237_, v_a_4240_, v_b_4241_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_4254_ = _args[0];
lean_object* v___x_4255_ = _args[1];
lean_object* v_methods_4256_ = _args[2];
lean_object* v_config_4257_ = _args[3];
lean_object* v_inst_4258_ = _args[4];
lean_object* v_R_4259_ = _args[5];
lean_object* v_a_4260_ = _args[6];
lean_object* v_b_4261_ = _args[7];
lean_object* v_c_4262_ = _args[8];
lean_object* v___y_4263_ = _args[9];
lean_object* v___y_4264_ = _args[10];
lean_object* v___y_4265_ = _args[11];
lean_object* v___y_4266_ = _args[12];
lean_object* v___y_4267_ = _args[13];
lean_object* v___y_4268_ = _args[14];
lean_object* v___y_4269_ = _args[15];
lean_object* v___y_4270_ = _args[16];
lean_object* v___y_4271_ = _args[17];
lean_object* v___y_4272_ = _args[18];
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2(v_upperBound_4254_, v___x_4255_, v_methods_4256_, v_config_4257_, v_inst_4258_, v_R_4259_, v_a_4260_, v_b_4261_, v_c_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___x_4255_);
lean_dec(v_upperBound_4254_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2(lean_object* v_00_u03b2_4274_, lean_object* v_x_4275_, lean_object* v_x_4276_, lean_object* v_x_4277_){
_start:
{
lean_object* v___x_4278_; 
v___x_4278_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(v_x_4275_, v_x_4276_, v_x_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4279_, lean_object* v_x_4280_, size_t v_x_4281_, size_t v_x_4282_, lean_object* v_x_4283_, lean_object* v_x_4284_){
_start:
{
lean_object* v___x_4285_; 
v___x_4285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___redArg(v_x_4280_, v_x_4281_, v_x_4282_, v_x_4283_, v_x_4284_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4286_, lean_object* v_x_4287_, lean_object* v_x_4288_, lean_object* v_x_4289_, lean_object* v_x_4290_, lean_object* v_x_4291_){
_start:
{
size_t v_x_25169__boxed_4292_; size_t v_x_25170__boxed_4293_; lean_object* v_res_4294_; 
v_x_25169__boxed_4292_ = lean_unbox_usize(v_x_4288_);
lean_dec(v_x_4288_);
v_x_25170__boxed_4293_ = lean_unbox_usize(v_x_4289_);
lean_dec(v_x_4289_);
v_res_4294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3(v_00_u03b2_4286_, v_x_4287_, v_x_25169__boxed_4292_, v_x_25170__boxed_4293_, v_x_4290_, v_x_4291_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_4295_, lean_object* v_n_4296_, lean_object* v_k_4297_, lean_object* v_v_4298_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5___redArg(v_n_4296_, v_k_4297_, v_v_4298_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_4300_, size_t v_depth_4301_, lean_object* v_keys_4302_, lean_object* v_vals_4303_, lean_object* v_heq_4304_, lean_object* v_i_4305_, lean_object* v_entries_4306_){
_start:
{
lean_object* v___x_4307_; 
v___x_4307_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_4301_, v_keys_4302_, v_vals_4303_, v_i_4305_, v_entries_4306_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4308_, lean_object* v_depth_4309_, lean_object* v_keys_4310_, lean_object* v_vals_4311_, lean_object* v_heq_4312_, lean_object* v_i_4313_, lean_object* v_entries_4314_){
_start:
{
size_t v_depth_boxed_4315_; lean_object* v_res_4316_; 
v_depth_boxed_4315_ = lean_unbox_usize(v_depth_4309_);
lean_dec(v_depth_4309_);
v_res_4316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__6(v_00_u03b2_4308_, v_depth_boxed_4315_, v_keys_4310_, v_vals_4311_, v_heq_4312_, v_i_4313_, v_entries_4314_);
lean_dec_ref(v_vals_4311_);
lean_dec_ref(v_keys_4310_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_4317_, lean_object* v_x_4318_, lean_object* v_x_4319_, lean_object* v_x_4320_, lean_object* v_x_4321_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_x_4318_, v_x_4319_, v_x_4320_, v_x_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(lean_object* v_methods_4323_, lean_object* v_config_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4334_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteSimpCache___redArg___closed__1);
v___x_4335_ = lean_st_mk_ref(v___x_4334_);
v___x_4336_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go(v_methods_4323_, v_config_4324_, v___x_4335_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4345_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4339_ = v___x_4336_;
v_isShared_4340_ = v_isSharedCheck_4345_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4336_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4345_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4341_; lean_object* v___x_4343_; 
v___x_4341_ = lean_st_ref_get(v___x_4335_);
lean_dec(v___x_4335_);
lean_dec(v___x_4341_);
if (v_isShared_4340_ == 0)
{
v___x_4343_ = v___x_4339_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4337_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
else
{
lean_dec(v___x_4335_);
return v___x_4336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object* v_methods_4346_, lean_object* v_config_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps(v_methods_4346_, v_config_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
lean_dec(v_a_4353_);
lean_dec_ref(v_a_4352_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(lean_object* v_mvarId_4358_, lean_object* v_val_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v___x_4362_; lean_object* v_mctx_4363_; lean_object* v_cache_4364_; lean_object* v_zetaDeltaFVarIds_4365_; lean_object* v_postponed_4366_; lean_object* v_diag_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4395_; 
v___x_4362_ = lean_st_ref_take(v___y_4360_);
v_mctx_4363_ = lean_ctor_get(v___x_4362_, 0);
v_cache_4364_ = lean_ctor_get(v___x_4362_, 1);
v_zetaDeltaFVarIds_4365_ = lean_ctor_get(v___x_4362_, 2);
v_postponed_4366_ = lean_ctor_get(v___x_4362_, 3);
v_diag_4367_ = lean_ctor_get(v___x_4362_, 4);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4369_ = v___x_4362_;
v_isShared_4370_ = v_isSharedCheck_4395_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_diag_4367_);
lean_inc(v_postponed_4366_);
lean_inc(v_zetaDeltaFVarIds_4365_);
lean_inc(v_cache_4364_);
lean_inc(v_mctx_4363_);
lean_dec(v___x_4362_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4395_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v_depth_4371_; lean_object* v_levelAssignDepth_4372_; lean_object* v_lmvarCounter_4373_; lean_object* v_mvarCounter_4374_; lean_object* v_lDecls_4375_; lean_object* v_decls_4376_; lean_object* v_userNames_4377_; lean_object* v_lAssignment_4378_; lean_object* v_eAssignment_4379_; lean_object* v_dAssignment_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4394_; 
v_depth_4371_ = lean_ctor_get(v_mctx_4363_, 0);
v_levelAssignDepth_4372_ = lean_ctor_get(v_mctx_4363_, 1);
v_lmvarCounter_4373_ = lean_ctor_get(v_mctx_4363_, 2);
v_mvarCounter_4374_ = lean_ctor_get(v_mctx_4363_, 3);
v_lDecls_4375_ = lean_ctor_get(v_mctx_4363_, 4);
v_decls_4376_ = lean_ctor_get(v_mctx_4363_, 5);
v_userNames_4377_ = lean_ctor_get(v_mctx_4363_, 6);
v_lAssignment_4378_ = lean_ctor_get(v_mctx_4363_, 7);
v_eAssignment_4379_ = lean_ctor_get(v_mctx_4363_, 8);
v_dAssignment_4380_ = lean_ctor_get(v_mctx_4363_, 9);
v_isSharedCheck_4394_ = !lean_is_exclusive(v_mctx_4363_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4382_ = v_mctx_4363_;
v_isShared_4383_ = v_isSharedCheck_4394_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_dAssignment_4380_);
lean_inc(v_eAssignment_4379_);
lean_inc(v_lAssignment_4378_);
lean_inc(v_userNames_4377_);
lean_inc(v_decls_4376_);
lean_inc(v_lDecls_4375_);
lean_inc(v_mvarCounter_4374_);
lean_inc(v_lmvarCounter_4373_);
lean_inc(v_levelAssignDepth_4372_);
lean_inc(v_depth_4371_);
lean_dec(v_mctx_4363_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4394_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; lean_object* v___x_4386_; 
v___x_4384_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__1_spec__2___redArg(v_eAssignment_4379_, v_mvarId_4358_, v_val_4359_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 8, v___x_4384_);
v___x_4386_ = v___x_4382_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_depth_4371_);
lean_ctor_set(v_reuseFailAlloc_4393_, 1, v_levelAssignDepth_4372_);
lean_ctor_set(v_reuseFailAlloc_4393_, 2, v_lmvarCounter_4373_);
lean_ctor_set(v_reuseFailAlloc_4393_, 3, v_mvarCounter_4374_);
lean_ctor_set(v_reuseFailAlloc_4393_, 4, v_lDecls_4375_);
lean_ctor_set(v_reuseFailAlloc_4393_, 5, v_decls_4376_);
lean_ctor_set(v_reuseFailAlloc_4393_, 6, v_userNames_4377_);
lean_ctor_set(v_reuseFailAlloc_4393_, 7, v_lAssignment_4378_);
lean_ctor_set(v_reuseFailAlloc_4393_, 8, v___x_4384_);
lean_ctor_set(v_reuseFailAlloc_4393_, 9, v_dAssignment_4380_);
v___x_4386_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
lean_object* v___x_4388_; 
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 0, v___x_4386_);
v___x_4388_ = v___x_4369_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v___x_4386_);
lean_ctor_set(v_reuseFailAlloc_4392_, 1, v_cache_4364_);
lean_ctor_set(v_reuseFailAlloc_4392_, 2, v_zetaDeltaFVarIds_4365_);
lean_ctor_set(v_reuseFailAlloc_4392_, 3, v_postponed_4366_);
lean_ctor_set(v_reuseFailAlloc_4392_, 4, v_diag_4367_);
v___x_4388_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4389_ = lean_st_ref_set(v___y_4360_, v___x_4388_);
v___x_4390_ = lean_box(0);
v___x_4391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
return v___x_4391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg___boxed(lean_object* v_mvarId_4396_, lean_object* v_val_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_mvarId_4396_, v_val_4397_, v___y_4398_);
lean_dec(v___y_4398_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(lean_object* v_cls_4401_, lean_object* v_msg_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v_ref_4408_; lean_object* v___x_4409_; lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4454_; 
v_ref_4408_ = lean_ctor_get(v___y_4405_, 5);
v___x_4409_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4412_ = v___x_4409_;
v_isShared_4413_ = v_isSharedCheck_4454_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4409_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4454_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4414_; lean_object* v_traceState_4415_; lean_object* v_env_4416_; lean_object* v_nextMacroScope_4417_; lean_object* v_ngen_4418_; lean_object* v_auxDeclNGen_4419_; lean_object* v_cache_4420_; lean_object* v_messages_4421_; lean_object* v_infoState_4422_; lean_object* v_snapshotTasks_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4453_; 
v___x_4414_ = lean_st_ref_take(v___y_4406_);
v_traceState_4415_ = lean_ctor_get(v___x_4414_, 4);
v_env_4416_ = lean_ctor_get(v___x_4414_, 0);
v_nextMacroScope_4417_ = lean_ctor_get(v___x_4414_, 1);
v_ngen_4418_ = lean_ctor_get(v___x_4414_, 2);
v_auxDeclNGen_4419_ = lean_ctor_get(v___x_4414_, 3);
v_cache_4420_ = lean_ctor_get(v___x_4414_, 5);
v_messages_4421_ = lean_ctor_get(v___x_4414_, 6);
v_infoState_4422_ = lean_ctor_get(v___x_4414_, 7);
v_snapshotTasks_4423_ = lean_ctor_get(v___x_4414_, 8);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4425_ = v___x_4414_;
v_isShared_4426_ = v_isSharedCheck_4453_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_snapshotTasks_4423_);
lean_inc(v_infoState_4422_);
lean_inc(v_messages_4421_);
lean_inc(v_cache_4420_);
lean_inc(v_traceState_4415_);
lean_inc(v_auxDeclNGen_4419_);
lean_inc(v_ngen_4418_);
lean_inc(v_nextMacroScope_4417_);
lean_inc(v_env_4416_);
lean_dec(v___x_4414_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4453_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
uint64_t v_tid_4427_; lean_object* v_traces_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4452_; 
v_tid_4427_ = lean_ctor_get_uint64(v_traceState_4415_, sizeof(void*)*1);
v_traces_4428_ = lean_ctor_get(v_traceState_4415_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v_traceState_4415_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4430_ = v_traceState_4415_;
v_isShared_4431_ = v_isSharedCheck_4452_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_traces_4428_);
lean_dec(v_traceState_4415_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4452_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4432_; double v___x_4433_; uint8_t v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4442_; 
v___x_4432_ = lean_box(0);
v___x_4433_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_4434_ = 0;
v___x_4435_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4436_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4436_, 0, v_cls_4401_);
lean_ctor_set(v___x_4436_, 1, v___x_4432_);
lean_ctor_set(v___x_4436_, 2, v___x_4435_);
lean_ctor_set_float(v___x_4436_, sizeof(void*)*3, v___x_4433_);
lean_ctor_set_float(v___x_4436_, sizeof(void*)*3 + 8, v___x_4433_);
lean_ctor_set_uint8(v___x_4436_, sizeof(void*)*3 + 16, v___x_4434_);
v___x_4437_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_4438_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4436_);
lean_ctor_set(v___x_4438_, 1, v_a_4410_);
lean_ctor_set(v___x_4438_, 2, v___x_4437_);
lean_inc(v_ref_4408_);
v___x_4439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4439_, 0, v_ref_4408_);
lean_ctor_set(v___x_4439_, 1, v___x_4438_);
v___x_4440_ = l_Lean_PersistentArray_push___redArg(v_traces_4428_, v___x_4439_);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 0, v___x_4440_);
v___x_4442_ = v___x_4430_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4440_);
lean_ctor_set_uint64(v_reuseFailAlloc_4451_, sizeof(void*)*1, v_tid_4427_);
v___x_4442_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
lean_object* v___x_4444_; 
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 4, v___x_4442_);
v___x_4444_ = v___x_4425_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_env_4416_);
lean_ctor_set(v_reuseFailAlloc_4450_, 1, v_nextMacroScope_4417_);
lean_ctor_set(v_reuseFailAlloc_4450_, 2, v_ngen_4418_);
lean_ctor_set(v_reuseFailAlloc_4450_, 3, v_auxDeclNGen_4419_);
lean_ctor_set(v_reuseFailAlloc_4450_, 4, v___x_4442_);
lean_ctor_set(v_reuseFailAlloc_4450_, 5, v_cache_4420_);
lean_ctor_set(v_reuseFailAlloc_4450_, 6, v_messages_4421_);
lean_ctor_set(v_reuseFailAlloc_4450_, 7, v_infoState_4422_);
lean_ctor_set(v_reuseFailAlloc_4450_, 8, v_snapshotTasks_4423_);
v___x_4444_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4448_; 
v___x_4445_ = lean_st_ref_set(v___y_4406_, v___x_4444_);
v___x_4446_ = lean_box(0);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4446_);
v___x_4448_ = v___x_4412_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4446_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg___boxed(lean_object* v_cls_4455_, lean_object* v_msg_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_4455_, v_msg_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(lean_object* v_upperBound_4463_, lean_object* v___x_4464_, lean_object* v_methods_4465_, lean_object* v_config_4466_, lean_object* v_a_4467_, lean_object* v_b_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v___y_4480_; uint8_t v___x_4502_; 
v___x_4502_ = lean_nat_dec_lt(v_a_4467_, v_upperBound_4463_);
if (v___x_4502_ == 0)
{
lean_object* v___x_4503_; 
lean_dec(v_a_4467_);
lean_dec_ref(v_config_4466_);
lean_dec_ref(v_methods_4465_);
v___x_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4503_, 0, v_b_4468_);
return v___x_4503_;
}
else
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v_type_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4504_ = lean_st_ref_take(v___y_4469_);
v___x_4505_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
v___x_4506_ = lean_st_ref_set(v___y_4469_, v___x_4505_);
v___x_4507_ = lean_array_fget_borrowed(v___x_4464_, v_a_4467_);
v_type_4508_ = lean_ctor_get(v___x_4507_, 1);
v___x_4509_ = lean_unsigned_to_nat(0u);
v___x_4510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
lean_ctor_set(v___x_4510_, 1, v___x_4504_);
lean_inc_ref(v_type_4508_);
v___x_4511_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_4511_, 0, v_type_4508_);
lean_inc_ref(v_config_4466_);
lean_inc_ref(v_methods_4465_);
v___x_4512_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_4511_, v_methods_4465_, v_config_4466_, v___x_4510_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v_a_4513_; lean_object* v_snd_4514_; lean_object* v_fst_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4604_; 
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc(v_a_4513_);
lean_dec_ref_known(v___x_4512_, 1);
v_snd_4514_ = lean_ctor_get(v_a_4513_, 1);
v_fst_4515_ = lean_ctor_get(v_a_4513_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v_a_4513_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4517_ = v_a_4513_;
v_isShared_4518_ = v_isSharedCheck_4604_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_snd_4514_);
lean_inc(v_fst_4515_);
lean_dec(v_a_4513_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4604_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v_cache_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4602_; 
v_cache_4519_ = lean_ctor_get(v_snd_4514_, 1);
v_isSharedCheck_4602_ = !lean_is_exclusive(v_snd_4514_);
if (v_isSharedCheck_4602_ == 0)
{
lean_object* v_unused_4603_; 
v_unused_4603_ = lean_ctor_get(v_snd_4514_, 0);
lean_dec(v_unused_4603_);
v___x_4521_ = v_snd_4514_;
v_isShared_4522_ = v_isSharedCheck_4602_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_cache_4519_);
lean_dec(v_snd_4514_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4602_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4523_ = lean_st_ref_set(v___y_4469_, v_cache_4519_);
lean_inc(v___x_4507_);
v___x_4524_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v___x_4507_, v_fst_4515_);
lean_dec(v_fst_4515_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; lean_object* v_snd_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4592_; 
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_a_4525_);
lean_dec_ref_known(v___x_4524_, 1);
v_snd_4526_ = lean_ctor_get(v_b_4468_, 1);
v_isSharedCheck_4592_ = !lean_is_exclusive(v_b_4468_);
if (v_isSharedCheck_4592_ == 0)
{
lean_object* v_unused_4593_; 
v_unused_4593_ = lean_ctor_get(v_b_4468_, 0);
lean_dec(v_unused_4593_);
v___x_4528_ = v_b_4468_;
v_isShared_4529_ = v_isSharedCheck_4592_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_snd_4526_);
lean_dec(v_b_4468_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4592_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v_type_4530_; lean_object* v_value_4531_; uint8_t v___x_4532_; 
v_type_4530_ = lean_ctor_get(v_a_4525_, 1);
v_value_4531_ = lean_ctor_get(v_a_4525_, 2);
lean_inc_ref(v_type_4530_);
v___x_4532_ = l_Lean_Expr_isFalse(v_type_4530_);
if (v___x_4532_ == 0)
{
lean_object* v___x_4533_; lean_object* v___f_4534_; uint8_t v___x_4565_; 
lean_del_object(v___x_4528_);
v___x_4533_ = lean_box(0);
lean_inc(v_a_4525_);
lean_inc(v_snd_4526_);
v___f_4534_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0___boxed), 14, 3);
lean_closure_set(v___f_4534_, 0, v_snd_4526_);
lean_closure_set(v___f_4534_, 1, v_a_4525_);
lean_closure_set(v___f_4534_, 2, v___x_4533_);
v___x_4565_ = lean_expr_eqv(v_type_4508_, v_type_4530_);
if (v___x_4565_ == 0)
{
lean_inc_ref(v_type_4530_);
lean_dec(v_snd_4526_);
lean_dec(v_a_4525_);
goto v___jp_4538_;
}
else
{
if (v___x_4532_ == 0)
{
lean_object* v___x_4566_; lean_object* v___x_4567_; 
lean_dec_ref(v___f_4534_);
lean_del_object(v___x_4521_);
lean_del_object(v___x_4517_);
v___x_4566_ = lean_box(0);
v___x_4567_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__0(v_snd_4526_, v_a_4525_, v___x_4533_, v___x_4566_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
v___y_4480_ = v___x_4567_;
goto v___jp_4479_;
}
else
{
lean_inc_ref(v_type_4530_);
lean_dec(v_snd_4526_);
lean_dec(v_a_4525_);
goto v___jp_4538_;
}
}
v___jp_4535_:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4536_ = lean_box(0);
v___x_4537_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_4502_, v___f_4534_, v___x_4536_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
v___y_4480_ = v___x_4537_;
goto v___jp_4479_;
}
v___jp_4538_:
{
lean_object* v_options_4539_; uint8_t v_hasTrace_4540_; 
v_options_4539_ = lean_ctor_get(v___y_4476_, 2);
v_hasTrace_4540_ = lean_ctor_get_uint8(v_options_4539_, sizeof(void*)*1);
if (v_hasTrace_4540_ == 0)
{
lean_dec_ref(v_type_4530_);
lean_del_object(v___x_4521_);
lean_del_object(v___x_4517_);
goto v___jp_4535_;
}
else
{
lean_object* v_inheritedTraceOptions_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; uint8_t v___x_4544_; 
v_inheritedTraceOptions_4541_ = lean_ctor_get(v___y_4476_, 13);
v___x_4542_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_4543_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_4544_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4541_, v_options_4539_, v___x_4543_);
if (v___x_4544_ == 0)
{
lean_dec_ref(v_type_4530_);
lean_del_object(v___x_4521_);
lean_del_object(v___x_4517_);
goto v___jp_4535_;
}
else
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4548_; 
lean_inc_ref(v_type_4508_);
v___x_4545_ = l_Lean_MessageData_ofExpr(v_type_4508_);
v___x_4546_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_flatMapHyps___redArg___lam__5___closed__1);
if (v_isShared_4522_ == 0)
{
lean_ctor_set_tag(v___x_4521_, 7);
lean_ctor_set(v___x_4521_, 1, v___x_4546_);
lean_ctor_set(v___x_4521_, 0, v___x_4545_);
v___x_4548_ = v___x_4521_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4545_);
lean_ctor_set(v_reuseFailAlloc_4564_, 1, v___x_4546_);
v___x_4548_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
lean_object* v___x_4549_; lean_object* v___x_4551_; 
v___x_4549_ = l_Lean_MessageData_ofExpr(v_type_4530_);
if (v_isShared_4518_ == 0)
{
lean_ctor_set_tag(v___x_4517_, 7);
lean_ctor_set(v___x_4517_, 1, v___x_4549_);
lean_ctor_set(v___x_4517_, 0, v___x_4548_);
v___x_4551_ = v___x_4517_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v___x_4548_);
lean_ctor_set(v_reuseFailAlloc_4563_, 1, v___x_4549_);
v___x_4551_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
lean_object* v___x_4552_; 
v___x_4552_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v___x_4542_, v___x_4551_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v_a_4553_; lean_object* v___x_4554_; 
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
lean_inc(v_a_4553_);
lean_dec_ref_known(v___x_4552_, 1);
v___x_4554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__2___redArg___lam__1(v___x_4502_, v___f_4534_, v_a_4553_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
v___y_4480_ = v___x_4554_;
goto v___jp_4479_;
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec_ref(v___f_4534_);
lean_dec(v_a_4467_);
lean_dec_ref(v_config_4466_);
lean_dec_ref(v_methods_4465_);
v_a_4555_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4552_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4552_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
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
}
}
}
}
else
{
lean_object* v___x_4568_; lean_object* v_goal_4569_; lean_object* v___x_4570_; 
lean_inc_ref(v_value_4531_);
lean_dec(v_a_4525_);
lean_del_object(v___x_4521_);
lean_del_object(v___x_4517_);
lean_dec(v_a_4467_);
lean_dec_ref(v_config_4466_);
lean_dec_ref(v_methods_4465_);
v___x_4568_ = lean_st_ref_get(v___y_4471_);
v_goal_4569_ = lean_ctor_get(v___x_4568_, 4);
lean_inc(v_goal_4569_);
lean_dec(v___x_4568_);
v___x_4570_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_goal_4569_, v_value_4531_, v___y_4475_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4582_; 
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4582_ == 0)
{
lean_object* v_unused_4583_; 
v_unused_4583_ = lean_ctor_get(v___x_4570_, 0);
lean_dec(v_unused_4583_);
v___x_4572_ = v___x_4570_;
v_isShared_4573_ = v_isSharedCheck_4582_;
goto v_resetjp_4571_;
}
else
{
lean_dec(v___x_4570_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4582_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4577_; 
v___x_4574_ = lean_box(v___x_4532_);
v___x_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4574_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 0, v___x_4575_);
v___x_4577_ = v___x_4528_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4575_);
lean_ctor_set(v_reuseFailAlloc_4581_, 1, v_snd_4526_);
v___x_4577_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
lean_object* v___x_4579_; 
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 0, v___x_4577_);
v___x_4579_ = v___x_4572_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v___x_4577_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_del_object(v___x_4528_);
lean_dec(v_snd_4526_);
v_a_4584_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4570_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4570_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
}
}
}
else
{
lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4601_; 
lean_del_object(v___x_4521_);
lean_del_object(v___x_4517_);
lean_dec_ref(v_b_4468_);
lean_dec(v_a_4467_);
lean_dec_ref(v_config_4466_);
lean_dec_ref(v_methods_4465_);
v_a_4594_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4596_ = v___x_4524_;
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_dec(v___x_4524_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4599_; 
if (v_isShared_4597_ == 0)
{
v___x_4599_ = v___x_4596_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_a_4594_);
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
}
}
else
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
lean_dec_ref(v_b_4468_);
lean_dec(v_a_4467_);
lean_dec_ref(v_config_4466_);
lean_dec_ref(v_methods_4465_);
v_a_4605_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4512_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4512_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
}
v___jp_4479_:
{
if (lean_obj_tag(v___y_4480_) == 0)
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4493_; 
v_a_4481_ = lean_ctor_get(v___y_4480_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___y_4480_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4483_ = v___y_4480_;
v_isShared_4484_ = v_isSharedCheck_4493_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___y_4480_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4493_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
if (lean_obj_tag(v_a_4481_) == 0)
{
lean_object* v_a_4485_; lean_object* v___x_4487_; 
lean_dec(v_a_4467_);
lean_dec_ref(v_config_4466_);
lean_dec_ref(v_methods_4465_);
v_a_4485_ = lean_ctor_get(v_a_4481_, 0);
lean_inc(v_a_4485_);
lean_dec_ref_known(v_a_4481_, 1);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 0, v_a_4485_);
v___x_4487_ = v___x_4483_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4485_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
lean_del_object(v___x_4483_);
v_a_4489_ = lean_ctor_get(v_a_4481_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v_a_4481_, 1);
v___x_4490_ = lean_unsigned_to_nat(1u);
v___x_4491_ = lean_nat_add(v_a_4467_, v___x_4490_);
lean_dec(v_a_4467_);
v_a_4467_ = v___x_4491_;
v_b_4468_ = v_a_4489_;
goto _start;
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v_a_4467_);
lean_dec_ref(v_config_4466_);
lean_dec_ref(v_methods_4465_);
v_a_4494_ = lean_ctor_get(v___y_4480_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___y_4480_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___y_4480_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___y_4480_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg___boxed(lean_object* v_upperBound_4613_, lean_object* v___x_4614_, lean_object* v_methods_4615_, lean_object* v_config_4616_, lean_object* v_a_4617_, lean_object* v_b_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(v_upperBound_4613_, v___x_4614_, v_methods_4615_, v_config_4616_, v_a_4617_, v_b_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
lean_dec(v___y_4619_);
lean_dec_ref(v___x_4614_);
lean_dec(v_upperBound_4613_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(lean_object* v_methods_4630_, lean_object* v_config_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v___x_4642_; lean_object* v_hypotheses_4643_; lean_object* v___x_4644_; lean_object* v_newHyps_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4642_ = lean_st_ref_get(v_a_4634_);
v_hypotheses_4643_ = lean_ctor_get(v___x_4642_, 5);
lean_inc_ref(v_hypotheses_4643_);
lean_dec(v___x_4642_);
v___x_4644_ = lean_array_get_size(v_hypotheses_4643_);
v_newHyps_4645_ = lean_mk_empty_array_with_capacity(v___x_4644_);
v___x_4646_ = lean_unsigned_to_nat(0u);
v___x_4647_ = lean_box(0);
v___x_4648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
lean_ctor_set(v___x_4648_, 1, v_newHyps_4645_);
v___x_4649_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(v___x_4644_, v_hypotheses_4643_, v_methods_4630_, v_config_4631_, v___x_4646_, v___x_4648_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
lean_dec_ref(v_hypotheses_4643_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4681_; 
v_a_4650_ = lean_ctor_get(v___x_4649_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4652_ = v___x_4649_;
v_isShared_4653_ = v_isSharedCheck_4681_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4649_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4681_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v_fst_4654_; 
v_fst_4654_ = lean_ctor_get(v_a_4650_, 0);
if (lean_obj_tag(v_fst_4654_) == 0)
{
lean_object* v_snd_4655_; lean_object* v___x_4656_; lean_object* v_rewriteSimpCache_4657_; lean_object* v_rewriteDSimpCache_4658_; lean_object* v_acCache_4659_; lean_object* v_typeAnalysis_4660_; lean_object* v_goal_4661_; uint8_t v_didChange_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4675_; 
v_snd_4655_ = lean_ctor_get(v_a_4650_, 1);
lean_inc(v_snd_4655_);
lean_dec(v_a_4650_);
v___x_4656_ = lean_st_ref_take(v_a_4634_);
v_rewriteSimpCache_4657_ = lean_ctor_get(v___x_4656_, 0);
v_rewriteDSimpCache_4658_ = lean_ctor_get(v___x_4656_, 1);
v_acCache_4659_ = lean_ctor_get(v___x_4656_, 2);
v_typeAnalysis_4660_ = lean_ctor_get(v___x_4656_, 3);
v_goal_4661_ = lean_ctor_get(v___x_4656_, 4);
v_didChange_4662_ = lean_ctor_get_uint8(v___x_4656_, sizeof(void*)*6);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4656_);
if (v_isSharedCheck_4675_ == 0)
{
lean_object* v_unused_4676_; 
v_unused_4676_ = lean_ctor_get(v___x_4656_, 5);
lean_dec(v_unused_4676_);
v___x_4664_ = v___x_4656_;
v_isShared_4665_ = v_isSharedCheck_4675_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_goal_4661_);
lean_inc(v_typeAnalysis_4660_);
lean_inc(v_acCache_4659_);
lean_inc(v_rewriteDSimpCache_4658_);
lean_inc(v_rewriteSimpCache_4657_);
lean_dec(v___x_4656_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4675_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
lean_ctor_set(v___x_4664_, 5, v_snd_4655_);
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_rewriteSimpCache_4657_);
lean_ctor_set(v_reuseFailAlloc_4674_, 1, v_rewriteDSimpCache_4658_);
lean_ctor_set(v_reuseFailAlloc_4674_, 2, v_acCache_4659_);
lean_ctor_set(v_reuseFailAlloc_4674_, 3, v_typeAnalysis_4660_);
lean_ctor_set(v_reuseFailAlloc_4674_, 4, v_goal_4661_);
lean_ctor_set(v_reuseFailAlloc_4674_, 5, v_snd_4655_);
lean_ctor_set_uint8(v_reuseFailAlloc_4674_, sizeof(void*)*6, v_didChange_4662_);
v___x_4667_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
lean_object* v___x_4668_; uint8_t v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4672_; 
v___x_4668_ = lean_st_ref_set(v_a_4634_, v___x_4667_);
v___x_4669_ = 0;
v___x_4670_ = lean_box(v___x_4669_);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 0, v___x_4670_);
v___x_4672_ = v___x_4652_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v___x_4670_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
}
}
else
{
lean_object* v_val_4677_; lean_object* v___x_4679_; 
lean_inc_ref(v_fst_4654_);
lean_dec(v_a_4650_);
v_val_4677_ = lean_ctor_get(v_fst_4654_, 0);
lean_inc(v_val_4677_);
lean_dec_ref_known(v_fst_4654_, 1);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 0, v_val_4677_);
v___x_4679_ = v___x_4652_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_val_4677_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
else
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4689_; 
v_a_4682_ = lean_ctor_get(v___x_4649_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4684_ = v___x_4649_;
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4649_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go___boxed(lean_object* v_methods_4690_, lean_object* v_config_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_){
_start:
{
lean_object* v_res_4702_; 
v_res_4702_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_4690_, v_config_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_);
lean_dec(v_a_4700_);
lean_dec_ref(v_a_4699_);
lean_dec(v_a_4698_);
lean_dec_ref(v_a_4697_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
lean_dec(v_a_4694_);
lean_dec_ref(v_a_4693_);
lean_dec(v_a_4692_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(lean_object* v_cls_4703_, lean_object* v_msg_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v___x_4715_; 
v___x_4715_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___redArg(v_cls_4703_, v_msg_4704_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
return v___x_4715_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0___boxed(lean_object* v_cls_4716_, lean_object* v_msg_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__0(v_cls_4716_, v_msg_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec(v___y_4718_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(lean_object* v_mvarId_4729_, lean_object* v_val_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v___x_4741_; 
v___x_4741_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___redArg(v_mvarId_4729_, v_val_4730_, v___y_4737_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1___boxed(lean_object* v_mvarId_4742_, lean_object* v_val_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__1(v_mvarId_4742_, v_val_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
lean_dec(v___y_4752_);
lean_dec_ref(v___y_4751_);
lean_dec(v___y_4750_);
lean_dec_ref(v___y_4749_);
lean_dec(v___y_4748_);
lean_dec_ref(v___y_4747_);
lean_dec(v___y_4746_);
lean_dec_ref(v___y_4745_);
lean_dec(v___y_4744_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2(lean_object* v_upperBound_4755_, lean_object* v___x_4756_, lean_object* v_methods_4757_, lean_object* v_config_4758_, lean_object* v_inst_4759_, lean_object* v_R_4760_, lean_object* v_a_4761_, lean_object* v_b_4762_, lean_object* v_c_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_){
_start:
{
lean_object* v___x_4774_; 
v___x_4774_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___redArg(v_upperBound_4755_, v___x_4756_, v_methods_4757_, v_config_4758_, v_a_4761_, v_b_4762_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_4775_ = _args[0];
lean_object* v___x_4776_ = _args[1];
lean_object* v_methods_4777_ = _args[2];
lean_object* v_config_4778_ = _args[3];
lean_object* v_inst_4779_ = _args[4];
lean_object* v_R_4780_ = _args[5];
lean_object* v_a_4781_ = _args[6];
lean_object* v_b_4782_ = _args[7];
lean_object* v_c_4783_ = _args[8];
lean_object* v___y_4784_ = _args[9];
lean_object* v___y_4785_ = _args[10];
lean_object* v___y_4786_ = _args[11];
lean_object* v___y_4787_ = _args[12];
lean_object* v___y_4788_ = _args[13];
lean_object* v___y_4789_ = _args[14];
lean_object* v___y_4790_ = _args[15];
lean_object* v___y_4791_ = _args[16];
lean_object* v___y_4792_ = _args[17];
lean_object* v___y_4793_ = _args[18];
_start:
{
lean_object* v_res_4794_; 
v_res_4794_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go_spec__2(v_upperBound_4775_, v___x_4776_, v_methods_4777_, v_config_4778_, v_inst_4779_, v_R_4780_, v_a_4781_, v_b_4782_, v_c_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
lean_dec(v___y_4792_);
lean_dec_ref(v___y_4791_);
lean_dec(v___y_4790_);
lean_dec_ref(v___y_4789_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___y_4784_);
lean_dec_ref(v___x_4776_);
lean_dec(v_upperBound_4775_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(lean_object* v_methods_4795_, lean_object* v_config_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_){
_start:
{
lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4806_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_takeRewriteDSimpCache___redArg___closed__1);
v___x_4807_ = lean_st_mk_ref(v___x_4806_);
v___x_4808_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps_go(v_methods_4795_, v_config_4796_, v___x_4807_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_object* v_a_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4817_; 
v_a_4809_ = lean_ctor_get(v___x_4808_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4808_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4811_ = v___x_4808_;
v_isShared_4812_ = v_isSharedCheck_4817_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_a_4809_);
lean_dec(v___x_4808_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4817_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4813_; lean_object* v___x_4815_; 
v___x_4813_ = lean_st_ref_get(v___x_4807_);
lean_dec(v___x_4807_);
lean_dec(v___x_4813_);
if (v_isShared_4812_ == 0)
{
v___x_4815_ = v___x_4811_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4809_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
else
{
lean_dec(v___x_4807_);
return v___x_4808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object* v_methods_4818_, lean_object* v_config_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps(v_methods_4818_, v_config_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
lean_dec(v_a_4825_);
lean_dec_ref(v_a_4824_);
lean_dec(v_a_4823_);
lean_dec_ref(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_a_4820_);
return v_res_4829_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4831_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0));
v___x_4832_ = l_Lean_stringToMessageData(v___x_4831_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(lean_object* v_name_4833_, lean_object* v_x_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4844_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1);
v___x_4845_ = l_Lean_MessageData_ofName(v_name_4833_);
v___x_4846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4844_);
lean_ctor_set(v___x_4846_, 1, v___x_4845_);
v___x_4847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4846_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(lean_object* v_name_4848_, lean_object* v_x_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(v_name_4848_, v_x_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
lean_dec(v___y_4853_);
lean_dec_ref(v___y_4852_);
lean_dec(v___y_4851_);
lean_dec_ref(v___y_4850_);
lean_dec_ref(v_x_4849_);
return v_res_4859_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0(void){
_start:
{
lean_object* v___x_4860_; 
v___x_4860_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_4860_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1(void){
_start:
{
lean_object* v___x_4861_; lean_object* v___x_4862_; 
v___x_4861_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0);
v___x_4862_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_4861_);
return v___x_4862_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2(void){
_start:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4863_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1);
v___x_4864_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_4863_);
return v___x_4864_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3(void){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4865_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2);
v___x_4866_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_4865_);
return v___x_4866_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4(void){
_start:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4867_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3);
v___x_4868_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_4867_);
return v___x_4868_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5(void){
_start:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4869_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4);
v___x_4870_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_4869_);
return v___x_4870_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6(void){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4871_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5);
v___x_4872_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_4871_);
return v___x_4872_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7(void){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6);
v___x_4874_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_4873_);
return v___x_4874_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8(void){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7);
v___x_4876_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_4875_);
return v___x_4876_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10(void){
_start:
{
lean_object* v___x_4878_; double v___x_4879_; 
v___x_4878_ = lean_unsigned_to_nat(1000000000u);
v___x_4879_ = lean_float_of_nat(v___x_4878_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(lean_object* v_pass_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_){
_start:
{
lean_object* v___x_4890_; lean_object* v_toApplicative_4891_; lean_object* v_toFunctor_4892_; lean_object* v_toSeq_4893_; lean_object* v_toSeqLeft_4894_; lean_object* v_toSeqRight_4895_; lean_object* v___f_4896_; lean_object* v___f_4897_; lean_object* v___f_4898_; lean_object* v___f_4899_; lean_object* v___x_4900_; lean_object* v___f_4901_; lean_object* v___f_4902_; lean_object* v___f_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v_toApplicative_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_5048_; 
v___x_4890_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__1);
v_toApplicative_4891_ = lean_ctor_get(v___x_4890_, 0);
v_toFunctor_4892_ = lean_ctor_get(v_toApplicative_4891_, 0);
v_toSeq_4893_ = lean_ctor_get(v_toApplicative_4891_, 2);
v_toSeqLeft_4894_ = lean_ctor_get(v_toApplicative_4891_, 3);
v_toSeqRight_4895_ = lean_ctor_get(v_toApplicative_4891_, 4);
v___f_4896_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__2));
v___f_4897_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__3));
lean_inc_ref_n(v_toFunctor_4892_, 2);
v___f_4898_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4898_, 0, v_toFunctor_4892_);
v___f_4899_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4899_, 0, v_toFunctor_4892_);
v___x_4900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4900_, 0, v___f_4898_);
lean_ctor_set(v___x_4900_, 1, v___f_4899_);
lean_inc(v_toSeqRight_4895_);
v___f_4901_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4901_, 0, v_toSeqRight_4895_);
lean_inc(v_toSeqLeft_4894_);
v___f_4902_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4902_, 0, v_toSeqLeft_4894_);
lean_inc(v_toSeq_4893_);
v___f_4903_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4903_, 0, v_toSeq_4893_);
v___x_4904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4900_);
lean_ctor_set(v___x_4904_, 1, v___f_4896_);
lean_ctor_set(v___x_4904_, 2, v___f_4903_);
lean_ctor_set(v___x_4904_, 3, v___f_4902_);
lean_ctor_set(v___x_4904_, 4, v___f_4901_);
v___x_4905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
lean_ctor_set(v___x_4905_, 1, v___f_4897_);
v___x_4906_ = l_StateRefT_x27_instMonad___redArg(v___x_4905_);
v_toApplicative_4907_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_5048_ == 0)
{
lean_object* v_unused_5049_; 
v_unused_5049_ = lean_ctor_get(v___x_4906_, 1);
lean_dec(v_unused_5049_);
v___x_4909_ = v___x_4906_;
v_isShared_4910_ = v_isSharedCheck_5048_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_toApplicative_4907_);
lean_dec(v___x_4906_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_5048_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v_toFunctor_4911_; lean_object* v_toSeq_4912_; lean_object* v_toSeqLeft_4913_; lean_object* v_toSeqRight_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_5046_; 
v_toFunctor_4911_ = lean_ctor_get(v_toApplicative_4907_, 0);
v_toSeq_4912_ = lean_ctor_get(v_toApplicative_4907_, 2);
v_toSeqLeft_4913_ = lean_ctor_get(v_toApplicative_4907_, 3);
v_toSeqRight_4914_ = lean_ctor_get(v_toApplicative_4907_, 4);
v_isSharedCheck_5046_ = !lean_is_exclusive(v_toApplicative_4907_);
if (v_isSharedCheck_5046_ == 0)
{
lean_object* v_unused_5047_; 
v_unused_5047_ = lean_ctor_get(v_toApplicative_4907_, 1);
lean_dec(v_unused_5047_);
v___x_4916_ = v_toApplicative_4907_;
v_isShared_4917_ = v_isSharedCheck_5046_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_toSeqRight_4914_);
lean_inc(v_toSeqLeft_4913_);
lean_inc(v_toSeq_4912_);
lean_inc(v_toFunctor_4911_);
lean_dec(v_toApplicative_4907_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_5046_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___f_4918_; lean_object* v___f_4919_; lean_object* v___f_4920_; lean_object* v___f_4921_; lean_object* v___x_4922_; lean_object* v___f_4923_; lean_object* v___f_4924_; lean_object* v___f_4925_; lean_object* v___x_4927_; 
v___f_4918_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__4));
v___f_4919_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__5));
lean_inc_ref(v_toFunctor_4911_);
v___f_4920_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4920_, 0, v_toFunctor_4911_);
v___f_4921_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4921_, 0, v_toFunctor_4911_);
v___x_4922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4922_, 0, v___f_4920_);
lean_ctor_set(v___x_4922_, 1, v___f_4921_);
v___f_4923_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4923_, 0, v_toSeqRight_4914_);
v___f_4924_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4924_, 0, v_toSeqLeft_4913_);
v___f_4925_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4925_, 0, v_toSeq_4912_);
if (v_isShared_4917_ == 0)
{
lean_ctor_set(v___x_4916_, 4, v___f_4923_);
lean_ctor_set(v___x_4916_, 3, v___f_4924_);
lean_ctor_set(v___x_4916_, 2, v___f_4925_);
lean_ctor_set(v___x_4916_, 1, v___f_4918_);
lean_ctor_set(v___x_4916_, 0, v___x_4922_);
v___x_4927_ = v___x_4916_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v___x_4922_);
lean_ctor_set(v_reuseFailAlloc_5045_, 1, v___f_4918_);
lean_ctor_set(v_reuseFailAlloc_5045_, 2, v___f_4925_);
lean_ctor_set(v_reuseFailAlloc_5045_, 3, v___f_4924_);
lean_ctor_set(v_reuseFailAlloc_5045_, 4, v___f_4923_);
v___x_4927_ = v_reuseFailAlloc_5045_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
lean_object* v___x_4929_; 
if (v_isShared_4910_ == 0)
{
lean_ctor_set(v___x_4909_, 1, v___f_4919_);
lean_ctor_set(v___x_4909_, 0, v___x_4927_);
v___x_4929_ = v___x_4909_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v___x_4927_);
lean_ctor_set(v_reuseFailAlloc_5044_, 1, v___f_4919_);
v___x_4929_ = v_reuseFailAlloc_5044_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v_toMonadRef_4936_; lean_object* v___x_4937_; lean_object* v_options_4938_; uint8_t v_hasTrace_4939_; 
v___x_4930_ = l_StateRefT_x27_instMonad___redArg(v___x_4929_);
v___x_4931_ = l_ReaderT_instMonad___redArg(v___x_4930_);
v___x_4932_ = l_StateRefT_x27_instMonad___redArg(v___x_4931_);
v___x_4933_ = l_ReaderT_instMonad___redArg(v___x_4932_);
v___x_4934_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__13);
v___x_4935_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__28);
v_toMonadRef_4936_ = lean_ctor_get(v___x_4935_, 0);
v___x_4937_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8);
v_options_4938_ = lean_ctor_get(v_a_4887_, 2);
v_hasTrace_4939_ = lean_ctor_get_uint8(v_options_4938_, sizeof(void*)*1);
if (v_hasTrace_4939_ == 0)
{
lean_object* v_run_x27_4940_; lean_object* v___x_4941_; 
lean_dec_ref(v___x_4933_);
v_run_x27_4940_ = lean_ctor_get(v_pass_4880_, 1);
lean_inc_ref(v_run_x27_4940_);
lean_dec_ref(v_pass_4880_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
lean_inc(v_a_4882_);
lean_inc_ref(v_a_4881_);
v___x_4941_ = lean_apply_9(v_run_x27_4940_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, lean_box(0));
return v___x_4941_;
}
else
{
lean_object* v_name_4942_; lean_object* v_run_x27_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_5043_; 
v_name_4942_ = lean_ctor_get(v_pass_4880_, 0);
v_run_x27_4943_ = lean_ctor_get(v_pass_4880_, 1);
v_isSharedCheck_5043_ = !lean_is_exclusive(v_pass_4880_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_4945_ = v_pass_4880_;
v_isShared_4946_ = v_isSharedCheck_5043_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_run_x27_4943_);
lean_inc(v_name_4942_);
lean_dec(v_pass_4880_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_5043_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v_inheritedTraceOptions_4947_; lean_object* v___f_4948_; lean_object* v___f_4949_; lean_object* v___f_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; uint8_t v___x_4954_; lean_object* v___y_4956_; lean_object* v___y_4957_; lean_object* v_a_4958_; lean_object* v___y_4974_; lean_object* v___y_4975_; lean_object* v_a_4976_; 
v_inheritedTraceOptions_4947_ = lean_ctor_get(v_a_4887_, 13);
v___f_4948_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 11, 1);
lean_closure_set(v___f_4948_, 0, v_name_4942_);
v___f_4949_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__32);
v___f_4950_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9));
v___x_4951_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_4952_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_4953_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_4954_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4947_, v_options_4938_, v___x_4953_);
if (v___x_4954_ == 0)
{
lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; uint8_t v___x_5041_; 
v___x_5038_ = l_Lean_KVMap_instValueBool;
v___x_5039_ = l_Lean_trace_profiler;
v___x_5040_ = l_Lean_Option_get___redArg(v___x_5038_, v_options_4938_, v___x_5039_);
v___x_5041_ = lean_unbox(v___x_5040_);
lean_dec(v___x_5040_);
if (v___x_5041_ == 0)
{
lean_object* v___x_5042_; 
lean_dec_ref(v___f_4948_);
lean_del_object(v___x_4945_);
lean_dec_ref(v___x_4933_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
lean_inc(v_a_4882_);
lean_inc_ref(v_a_4881_);
v___x_5042_ = lean_apply_9(v_run_x27_4943_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, lean_box(0));
return v___x_5042_;
}
else
{
goto v___jp_4986_;
}
}
else
{
goto v___jp_4986_;
}
v___jp_4955_:
{
lean_object* v___x_4959_; double v___x_4960_; double v___x_4961_; double v___x_4962_; double v___x_4963_; double v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4968_; 
v___x_4959_ = lean_io_mono_nanos_now();
v___x_4960_ = lean_float_of_nat(v___y_4957_);
v___x_4961_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_4962_ = lean_float_div(v___x_4960_, v___x_4961_);
v___x_4963_ = lean_float_of_nat(v___x_4959_);
v___x_4964_ = lean_float_div(v___x_4963_, v___x_4961_);
v___x_4965_ = lean_box_float(v___x_4962_);
v___x_4966_ = lean_box_float(v___x_4964_);
if (v_isShared_4946_ == 0)
{
lean_ctor_set(v___x_4945_, 1, v___x_4966_);
lean_ctor_set(v___x_4945_, 0, v___x_4965_);
v___x_4968_ = v___x_4945_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v___x_4965_);
lean_ctor_set(v_reuseFailAlloc_4972_, 1, v___x_4966_);
v___x_4968_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
lean_object* v___x_4969_; lean_object* v___x_16945__overap_4970_; lean_object* v___x_4971_; 
v___x_4969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4969_, 0, v_a_4958_);
lean_ctor_set(v___x_4969_, 1, v___x_4968_);
lean_inc_ref(v_toMonadRef_4936_);
v___x_16945__overap_4970_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_4933_, v___x_4934_, v_toMonadRef_4936_, v___f_4949_, lean_box(0), v___x_4937_, v___f_4950_, v___x_4951_, v_hasTrace_4939_, v___x_4952_, v_options_4938_, v___x_4954_, v___y_4956_, v___f_4948_, v___x_4969_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
lean_inc(v_a_4882_);
lean_inc_ref(v_a_4881_);
v___x_4971_ = lean_apply_9(v___x_16945__overap_4970_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, lean_box(0));
return v___x_4971_;
}
}
v___jp_4973_:
{
lean_object* v___x_4977_; double v___x_4978_; double v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_16966__overap_4984_; lean_object* v___x_4985_; 
v___x_4977_ = lean_io_get_num_heartbeats();
v___x_4978_ = lean_float_of_nat(v___y_4975_);
v___x_4979_ = lean_float_of_nat(v___x_4977_);
v___x_4980_ = lean_box_float(v___x_4978_);
v___x_4981_ = lean_box_float(v___x_4979_);
v___x_4982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4980_);
lean_ctor_set(v___x_4982_, 1, v___x_4981_);
v___x_4983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4983_, 0, v_a_4976_);
lean_ctor_set(v___x_4983_, 1, v___x_4982_);
lean_inc_ref(v_toMonadRef_4936_);
v___x_16966__overap_4984_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_4933_, v___x_4934_, v_toMonadRef_4936_, v___f_4949_, lean_box(0), v___x_4937_, v___f_4950_, v___x_4951_, v_hasTrace_4939_, v___x_4952_, v_options_4938_, v___x_4954_, v___y_4974_, v___f_4948_, v___x_4983_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
lean_inc(v_a_4882_);
lean_inc_ref(v_a_4881_);
v___x_4985_ = lean_apply_9(v___x_16966__overap_4984_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, lean_box(0));
return v___x_4985_;
}
v___jp_4986_:
{
lean_object* v___x_16922__overap_4987_; lean_object* v___x_4988_; 
lean_inc_ref(v___x_4933_);
v___x_16922__overap_4987_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_4933_, v___x_4934_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
lean_inc(v_a_4882_);
lean_inc_ref(v_a_4881_);
v___x_4988_ = lean_apply_9(v___x_16922__overap_4987_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, lean_box(0));
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v_a_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; uint8_t v___x_4993_; 
v_a_4989_ = lean_ctor_get(v___x_4988_, 0);
lean_inc(v_a_4989_);
lean_dec_ref_known(v___x_4988_, 1);
v___x_4990_ = l_Lean_KVMap_instValueBool;
v___x_4991_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4992_ = l_Lean_Option_get___redArg(v___x_4990_, v_options_4938_, v___x_4991_);
v___x_4993_ = lean_unbox(v___x_4992_);
lean_dec(v___x_4992_);
if (v___x_4993_ == 0)
{
lean_object* v___x_4994_; lean_object* v___x_4995_; 
v___x_4994_ = lean_io_mono_nanos_now();
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
lean_inc(v_a_4882_);
lean_inc_ref(v_a_4881_);
v___x_4995_ = lean_apply_9(v_run_x27_4943_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, lean_box(0));
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5003_; 
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4998_ = v___x_4995_;
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v___x_4995_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5001_; 
if (v_isShared_4999_ == 0)
{
lean_ctor_set_tag(v___x_4998_, 1);
v___x_5001_ = v___x_4998_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_a_4996_);
v___x_5001_ = v_reuseFailAlloc_5002_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
v___y_4956_ = v_a_4989_;
v___y_4957_ = v___x_4994_;
v_a_4958_ = v___x_5001_;
goto v___jp_4955_;
}
}
}
else
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5011_; 
v_a_5004_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5006_ = v___x_4995_;
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_4995_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
lean_ctor_set_tag(v___x_5006_, 0);
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_5004_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
v___y_4956_ = v_a_4989_;
v___y_4957_ = v___x_4994_;
v_a_4958_ = v___x_5009_;
goto v___jp_4955_;
}
}
}
}
else
{
lean_object* v___x_5012_; lean_object* v___x_5013_; 
lean_del_object(v___x_4945_);
v___x_5012_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
lean_inc(v_a_4886_);
lean_inc_ref(v_a_4885_);
lean_inc(v_a_4884_);
lean_inc_ref(v_a_4883_);
lean_inc(v_a_4882_);
lean_inc_ref(v_a_4881_);
v___x_5013_ = lean_apply_9(v_run_x27_4943_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, lean_box(0));
if (lean_obj_tag(v___x_5013_) == 0)
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
v_a_5014_ = lean_ctor_get(v___x_5013_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_5013_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v___x_5013_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_5013_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
lean_ctor_set_tag(v___x_5016_, 1);
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
v___y_4974_ = v_a_4989_;
v___y_4975_ = v___x_5012_;
v_a_4976_ = v___x_5019_;
goto v___jp_4973_;
}
}
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5029_; 
v_a_5022_ = lean_ctor_get(v___x_5013_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5013_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5024_ = v___x_5013_;
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_5013_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
lean_ctor_set_tag(v___x_5024_, 0);
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5022_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
v___y_4974_ = v_a_4989_;
v___y_4975_ = v___x_5012_;
v_a_4976_ = v___x_5027_;
goto v___jp_4973_;
}
}
}
}
}
else
{
lean_object* v_a_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5037_; 
lean_dec_ref(v___f_4948_);
lean_del_object(v___x_4945_);
lean_dec_ref(v_run_x27_4943_);
lean_dec_ref(v___x_4933_);
v_a_5030_ = lean_ctor_get(v___x_4988_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5032_ = v___x_4988_;
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_a_5030_);
lean_dec(v___x_4988_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5035_; 
if (v_isShared_5033_ == 0)
{
v___x_5035_ = v___x_5032_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_a_5030_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(lean_object* v_pass_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(v_pass_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_);
lean_dec(v_a_5058_);
lean_dec_ref(v_a_5057_);
lean_dec(v_a_5056_);
lean_dec_ref(v_a_5055_);
lean_dec(v_a_5054_);
lean_dec_ref(v_a_5053_);
lean_dec(v_a_5052_);
lean_dec_ref(v_a_5051_);
return v_res_5060_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
v___x_5061_ = lean_unsigned_to_nat(32u);
v___x_5062_ = lean_mk_empty_array_with_capacity(v___x_5061_);
v___x_5063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5063_, 0, v___x_5062_);
return v___x_5063_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; 
v___x_5064_ = ((size_t)5ULL);
v___x_5065_ = lean_unsigned_to_nat(0u);
v___x_5066_ = lean_unsigned_to_nat(32u);
v___x_5067_ = lean_mk_empty_array_with_capacity(v___x_5066_);
v___x_5068_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__0);
v___x_5069_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5069_, 0, v___x_5068_);
lean_ctor_set(v___x_5069_, 1, v___x_5067_);
lean_ctor_set(v___x_5069_, 2, v___x_5065_);
lean_ctor_set(v___x_5069_, 3, v___x_5065_);
lean_ctor_set_usize(v___x_5069_, 4, v___x_5064_);
return v___x_5069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(lean_object* v___y_5070_){
_start:
{
lean_object* v___x_5072_; lean_object* v_traceState_5073_; lean_object* v_traces_5074_; lean_object* v___x_5075_; lean_object* v_traceState_5076_; lean_object* v_env_5077_; lean_object* v_nextMacroScope_5078_; lean_object* v_ngen_5079_; lean_object* v_auxDeclNGen_5080_; lean_object* v_cache_5081_; lean_object* v_messages_5082_; lean_object* v_infoState_5083_; lean_object* v_snapshotTasks_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5103_; 
v___x_5072_ = lean_st_ref_get(v___y_5070_);
v_traceState_5073_ = lean_ctor_get(v___x_5072_, 4);
lean_inc_ref(v_traceState_5073_);
lean_dec(v___x_5072_);
v_traces_5074_ = lean_ctor_get(v_traceState_5073_, 0);
lean_inc_ref(v_traces_5074_);
lean_dec_ref(v_traceState_5073_);
v___x_5075_ = lean_st_ref_take(v___y_5070_);
v_traceState_5076_ = lean_ctor_get(v___x_5075_, 4);
v_env_5077_ = lean_ctor_get(v___x_5075_, 0);
v_nextMacroScope_5078_ = lean_ctor_get(v___x_5075_, 1);
v_ngen_5079_ = lean_ctor_get(v___x_5075_, 2);
v_auxDeclNGen_5080_ = lean_ctor_get(v___x_5075_, 3);
v_cache_5081_ = lean_ctor_get(v___x_5075_, 5);
v_messages_5082_ = lean_ctor_get(v___x_5075_, 6);
v_infoState_5083_ = lean_ctor_get(v___x_5075_, 7);
v_snapshotTasks_5084_ = lean_ctor_get(v___x_5075_, 8);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5086_ = v___x_5075_;
v_isShared_5087_ = v_isSharedCheck_5103_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_snapshotTasks_5084_);
lean_inc(v_infoState_5083_);
lean_inc(v_messages_5082_);
lean_inc(v_cache_5081_);
lean_inc(v_traceState_5076_);
lean_inc(v_auxDeclNGen_5080_);
lean_inc(v_ngen_5079_);
lean_inc(v_nextMacroScope_5078_);
lean_inc(v_env_5077_);
lean_dec(v___x_5075_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5103_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
uint64_t v_tid_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5101_; 
v_tid_5088_ = lean_ctor_get_uint64(v_traceState_5076_, sizeof(void*)*1);
v_isSharedCheck_5101_ = !lean_is_exclusive(v_traceState_5076_);
if (v_isSharedCheck_5101_ == 0)
{
lean_object* v_unused_5102_; 
v_unused_5102_ = lean_ctor_get(v_traceState_5076_, 0);
lean_dec(v_unused_5102_);
v___x_5090_ = v_traceState_5076_;
v_isShared_5091_ = v_isSharedCheck_5101_;
goto v_resetjp_5089_;
}
else
{
lean_dec(v_traceState_5076_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5101_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5092_; lean_object* v___x_5094_; 
v___x_5092_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___closed__1);
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 0, v___x_5092_);
v___x_5094_ = v___x_5090_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v___x_5092_);
lean_ctor_set_uint64(v_reuseFailAlloc_5100_, sizeof(void*)*1, v_tid_5088_);
v___x_5094_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
lean_object* v___x_5096_; 
if (v_isShared_5087_ == 0)
{
lean_ctor_set(v___x_5086_, 4, v___x_5094_);
v___x_5096_ = v___x_5086_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_env_5077_);
lean_ctor_set(v_reuseFailAlloc_5099_, 1, v_nextMacroScope_5078_);
lean_ctor_set(v_reuseFailAlloc_5099_, 2, v_ngen_5079_);
lean_ctor_set(v_reuseFailAlloc_5099_, 3, v_auxDeclNGen_5080_);
lean_ctor_set(v_reuseFailAlloc_5099_, 4, v___x_5094_);
lean_ctor_set(v_reuseFailAlloc_5099_, 5, v_cache_5081_);
lean_ctor_set(v_reuseFailAlloc_5099_, 6, v_messages_5082_);
lean_ctor_set(v_reuseFailAlloc_5099_, 7, v_infoState_5083_);
lean_ctor_set(v_reuseFailAlloc_5099_, 8, v_snapshotTasks_5084_);
v___x_5096_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
lean_object* v___x_5097_; lean_object* v___x_5098_; 
v___x_5097_ = lean_st_ref_set(v___y_5070_, v___x_5096_);
v___x_5098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5098_, 0, v_traces_5074_);
return v___x_5098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg___boxed(lean_object* v___y_5104_, lean_object* v___y_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_5104_);
lean_dec(v___y_5104_);
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_){
_start:
{
lean_object* v___x_5116_; 
v___x_5116_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_5114_);
return v___x_5116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___boxed(lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
lean_object* v_res_5126_; 
v_res_5126_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1(v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_);
lean_dec(v___y_5124_);
lean_dec_ref(v___y_5123_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec(v___y_5118_);
lean_dec_ref(v___y_5117_);
return v_res_5126_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(lean_object* v_opts_5127_, lean_object* v_opt_5128_){
_start:
{
lean_object* v_name_5129_; lean_object* v_defValue_5130_; lean_object* v_map_5131_; lean_object* v___x_5132_; 
v_name_5129_ = lean_ctor_get(v_opt_5128_, 0);
v_defValue_5130_ = lean_ctor_get(v_opt_5128_, 1);
v_map_5131_ = lean_ctor_get(v_opts_5127_, 0);
v___x_5132_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5131_, v_name_5129_);
if (lean_obj_tag(v___x_5132_) == 0)
{
uint8_t v___x_5133_; 
v___x_5133_ = lean_unbox(v_defValue_5130_);
return v___x_5133_;
}
else
{
lean_object* v_val_5134_; 
v_val_5134_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_val_5134_);
lean_dec_ref_known(v___x_5132_, 1);
if (lean_obj_tag(v_val_5134_) == 1)
{
uint8_t v_v_5135_; 
v_v_5135_ = lean_ctor_get_uint8(v_val_5134_, 0);
lean_dec_ref_known(v_val_5134_, 0);
return v_v_5135_;
}
else
{
uint8_t v___x_5136_; 
lean_dec(v_val_5134_);
v___x_5136_ = lean_unbox(v_defValue_5130_);
return v___x_5136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2___boxed(lean_object* v_opts_5137_, lean_object* v_opt_5138_){
_start:
{
uint8_t v_res_5139_; lean_object* v_r_5140_; 
v_res_5139_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_5137_, v_opt_5138_);
lean_dec_ref(v_opt_5138_);
lean_dec_ref(v_opts_5137_);
v_r_5140_ = lean_box(v_res_5139_);
return v_r_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(lean_object* v_cls_5141_, lean_object* v_msg_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_){
_start:
{
lean_object* v_ref_5148_; lean_object* v___x_5149_; lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5194_; 
v_ref_5148_ = lean_ctor_get(v___y_5145_, 5);
v___x_5149_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_);
v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5194_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5194_ == 0)
{
v___x_5152_ = v___x_5149_;
v_isShared_5153_ = v_isSharedCheck_5194_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v___x_5149_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5194_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5154_; lean_object* v_traceState_5155_; lean_object* v_env_5156_; lean_object* v_nextMacroScope_5157_; lean_object* v_ngen_5158_; lean_object* v_auxDeclNGen_5159_; lean_object* v_cache_5160_; lean_object* v_messages_5161_; lean_object* v_infoState_5162_; lean_object* v_snapshotTasks_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5193_; 
v___x_5154_ = lean_st_ref_take(v___y_5146_);
v_traceState_5155_ = lean_ctor_get(v___x_5154_, 4);
v_env_5156_ = lean_ctor_get(v___x_5154_, 0);
v_nextMacroScope_5157_ = lean_ctor_get(v___x_5154_, 1);
v_ngen_5158_ = lean_ctor_get(v___x_5154_, 2);
v_auxDeclNGen_5159_ = lean_ctor_get(v___x_5154_, 3);
v_cache_5160_ = lean_ctor_get(v___x_5154_, 5);
v_messages_5161_ = lean_ctor_get(v___x_5154_, 6);
v_infoState_5162_ = lean_ctor_get(v___x_5154_, 7);
v_snapshotTasks_5163_ = lean_ctor_get(v___x_5154_, 8);
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5154_);
if (v_isSharedCheck_5193_ == 0)
{
v___x_5165_ = v___x_5154_;
v_isShared_5166_ = v_isSharedCheck_5193_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_snapshotTasks_5163_);
lean_inc(v_infoState_5162_);
lean_inc(v_messages_5161_);
lean_inc(v_cache_5160_);
lean_inc(v_traceState_5155_);
lean_inc(v_auxDeclNGen_5159_);
lean_inc(v_ngen_5158_);
lean_inc(v_nextMacroScope_5157_);
lean_inc(v_env_5156_);
lean_dec(v___x_5154_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5193_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
uint64_t v_tid_5167_; lean_object* v_traces_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5192_; 
v_tid_5167_ = lean_ctor_get_uint64(v_traceState_5155_, sizeof(void*)*1);
v_traces_5168_ = lean_ctor_get(v_traceState_5155_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v_traceState_5155_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5170_ = v_traceState_5155_;
v_isShared_5171_ = v_isSharedCheck_5192_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_traces_5168_);
lean_dec(v_traceState_5155_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5192_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
lean_object* v___x_5172_; double v___x_5173_; uint8_t v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5182_; 
v___x_5172_ = lean_box(0);
v___x_5173_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
v___x_5174_ = 0;
v___x_5175_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5176_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5176_, 0, v_cls_5141_);
lean_ctor_set(v___x_5176_, 1, v___x_5172_);
lean_ctor_set(v___x_5176_, 2, v___x_5175_);
lean_ctor_set_float(v___x_5176_, sizeof(void*)*3, v___x_5173_);
lean_ctor_set_float(v___x_5176_, sizeof(void*)*3 + 8, v___x_5173_);
lean_ctor_set_uint8(v___x_5176_, sizeof(void*)*3 + 16, v___x_5174_);
v___x_5177_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__2));
v___x_5178_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5178_, 0, v___x_5176_);
lean_ctor_set(v___x_5178_, 1, v_a_5150_);
lean_ctor_set(v___x_5178_, 2, v___x_5177_);
lean_inc(v_ref_5148_);
v___x_5179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5179_, 0, v_ref_5148_);
lean_ctor_set(v___x_5179_, 1, v___x_5178_);
v___x_5180_ = l_Lean_PersistentArray_push___redArg(v_traces_5168_, v___x_5179_);
if (v_isShared_5171_ == 0)
{
lean_ctor_set(v___x_5170_, 0, v___x_5180_);
v___x_5182_ = v___x_5170_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5180_);
lean_ctor_set_uint64(v_reuseFailAlloc_5191_, sizeof(void*)*1, v_tid_5167_);
v___x_5182_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
lean_object* v___x_5184_; 
if (v_isShared_5166_ == 0)
{
lean_ctor_set(v___x_5165_, 4, v___x_5182_);
v___x_5184_ = v___x_5165_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_env_5156_);
lean_ctor_set(v_reuseFailAlloc_5190_, 1, v_nextMacroScope_5157_);
lean_ctor_set(v_reuseFailAlloc_5190_, 2, v_ngen_5158_);
lean_ctor_set(v_reuseFailAlloc_5190_, 3, v_auxDeclNGen_5159_);
lean_ctor_set(v_reuseFailAlloc_5190_, 4, v___x_5182_);
lean_ctor_set(v_reuseFailAlloc_5190_, 5, v_cache_5160_);
lean_ctor_set(v_reuseFailAlloc_5190_, 6, v_messages_5161_);
lean_ctor_set(v_reuseFailAlloc_5190_, 7, v_infoState_5162_);
lean_ctor_set(v_reuseFailAlloc_5190_, 8, v_snapshotTasks_5163_);
v___x_5184_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5188_; 
v___x_5185_ = lean_st_ref_set(v___y_5146_, v___x_5184_);
v___x_5186_ = lean_box(0);
if (v_isShared_5153_ == 0)
{
lean_ctor_set(v___x_5152_, 0, v___x_5186_);
v___x_5188_ = v___x_5152_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg___boxed(lean_object* v_cls_5195_, lean_object* v_msg_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_){
_start:
{
lean_object* v_res_5202_; 
v_res_5202_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_5195_, v_msg_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
lean_dec(v___y_5200_);
lean_dec_ref(v___y_5199_);
lean_dec(v___y_5198_);
lean_dec_ref(v___y_5197_);
return v_res_5202_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(lean_object* v_e_5203_){
_start:
{
if (lean_obj_tag(v_e_5203_) == 0)
{
uint8_t v___x_5204_; 
v___x_5204_ = 2;
return v___x_5204_;
}
else
{
lean_object* v_a_5205_; uint8_t v___x_5206_; 
v_a_5205_ = lean_ctor_get(v_e_5203_, 0);
v___x_5206_ = lean_unbox(v_a_5205_);
if (v___x_5206_ == 0)
{
uint8_t v___x_5207_; 
v___x_5207_ = 1;
return v___x_5207_;
}
else
{
uint8_t v___x_5208_; 
v___x_5208_ = 0;
return v___x_5208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5___boxed(lean_object* v_e_5209_){
_start:
{
uint8_t v_res_5210_; lean_object* v_r_5211_; 
v_res_5210_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_e_5209_);
lean_dec_ref(v_e_5209_);
v_r_5211_ = lean_box(v_res_5210_);
return v_r_5211_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(lean_object* v_x_5212_){
_start:
{
if (lean_obj_tag(v_x_5212_) == 0)
{
lean_object* v_a_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5221_; 
v_a_5214_ = lean_ctor_get(v_x_5212_, 0);
v_isSharedCheck_5221_ = !lean_is_exclusive(v_x_5212_);
if (v_isSharedCheck_5221_ == 0)
{
v___x_5216_ = v_x_5212_;
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_a_5214_);
lean_dec(v_x_5212_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v___x_5219_; 
if (v_isShared_5217_ == 0)
{
lean_ctor_set_tag(v___x_5216_, 1);
v___x_5219_ = v___x_5216_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5220_; 
v_reuseFailAlloc_5220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5220_, 0, v_a_5214_);
v___x_5219_ = v_reuseFailAlloc_5220_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
return v___x_5219_;
}
}
}
else
{
lean_object* v_a_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5229_; 
v_a_5222_ = lean_ctor_get(v_x_5212_, 0);
v_isSharedCheck_5229_ = !lean_is_exclusive(v_x_5212_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5224_ = v_x_5212_;
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_a_5222_);
lean_dec(v_x_5212_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
lean_object* v___x_5227_; 
if (v_isShared_5225_ == 0)
{
lean_ctor_set_tag(v___x_5224_, 0);
v___x_5227_ = v___x_5224_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5222_);
v___x_5227_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
return v___x_5227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg___boxed(lean_object* v_x_5230_, lean_object* v___y_5231_){
_start:
{
lean_object* v_res_5232_; 
v_res_5232_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_5230_);
return v_res_5232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(lean_object* v_opts_5233_, lean_object* v_opt_5234_){
_start:
{
lean_object* v_name_5235_; lean_object* v_defValue_5236_; lean_object* v_map_5237_; lean_object* v___x_5238_; 
v_name_5235_ = lean_ctor_get(v_opt_5234_, 0);
v_defValue_5236_ = lean_ctor_get(v_opt_5234_, 1);
v_map_5237_ = lean_ctor_get(v_opts_5233_, 0);
v___x_5238_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5237_, v_name_5235_);
if (lean_obj_tag(v___x_5238_) == 0)
{
lean_inc(v_defValue_5236_);
return v_defValue_5236_;
}
else
{
lean_object* v_val_5239_; 
v_val_5239_ = lean_ctor_get(v___x_5238_, 0);
lean_inc(v_val_5239_);
lean_dec_ref_known(v___x_5238_, 1);
if (lean_obj_tag(v_val_5239_) == 3)
{
lean_object* v_v_5240_; 
v_v_5240_ = lean_ctor_get(v_val_5239_, 0);
lean_inc(v_v_5240_);
lean_dec_ref_known(v_val_5239_, 1);
return v_v_5240_;
}
else
{
lean_dec(v_val_5239_);
lean_inc(v_defValue_5236_);
return v_defValue_5236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6___boxed(lean_object* v_opts_5241_, lean_object* v_opt_5242_){
_start:
{
lean_object* v_res_5243_; 
v_res_5243_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_5241_, v_opt_5242_);
lean_dec_ref(v_opt_5242_);
lean_dec_ref(v_opts_5241_);
return v_res_5243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(size_t v_sz_5244_, size_t v_i_5245_, lean_object* v_bs_5246_){
_start:
{
uint8_t v___x_5247_; 
v___x_5247_ = lean_usize_dec_lt(v_i_5245_, v_sz_5244_);
if (v___x_5247_ == 0)
{
return v_bs_5246_;
}
else
{
lean_object* v_v_5248_; lean_object* v_msg_5249_; lean_object* v___x_5250_; lean_object* v_bs_x27_5251_; size_t v___x_5252_; size_t v___x_5253_; lean_object* v___x_5254_; 
v_v_5248_ = lean_array_uget_borrowed(v_bs_5246_, v_i_5245_);
v_msg_5249_ = lean_ctor_get(v_v_5248_, 1);
lean_inc_ref(v_msg_5249_);
v___x_5250_ = lean_unsigned_to_nat(0u);
v_bs_x27_5251_ = lean_array_uset(v_bs_5246_, v_i_5245_, v___x_5250_);
v___x_5252_ = ((size_t)1ULL);
v___x_5253_ = lean_usize_add(v_i_5245_, v___x_5252_);
v___x_5254_ = lean_array_uset(v_bs_x27_5251_, v_i_5245_, v_msg_5249_);
v_i_5245_ = v___x_5253_;
v_bs_5246_ = v___x_5254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_5256_, lean_object* v_i_5257_, lean_object* v_bs_5258_){
_start:
{
size_t v_sz_boxed_5259_; size_t v_i_boxed_5260_; lean_object* v_res_5261_; 
v_sz_boxed_5259_ = lean_unbox_usize(v_sz_5256_);
lean_dec(v_sz_5256_);
v_i_boxed_5260_ = lean_unbox_usize(v_i_5257_);
lean_dec(v_i_5257_);
v_res_5261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_boxed_5259_, v_i_boxed_5260_, v_bs_5258_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(lean_object* v_oldTraces_5262_, lean_object* v_data_5263_, lean_object* v_ref_5264_, lean_object* v_msg_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_){
_start:
{
lean_object* v_fileName_5271_; lean_object* v_fileMap_5272_; lean_object* v_options_5273_; lean_object* v_currRecDepth_5274_; lean_object* v_maxRecDepth_5275_; lean_object* v_ref_5276_; lean_object* v_currNamespace_5277_; lean_object* v_openDecls_5278_; lean_object* v_initHeartbeats_5279_; lean_object* v_maxHeartbeats_5280_; lean_object* v_quotContext_5281_; lean_object* v_currMacroScope_5282_; uint8_t v_diag_5283_; lean_object* v_cancelTk_x3f_5284_; uint8_t v_suppressElabErrors_5285_; lean_object* v_inheritedTraceOptions_5286_; lean_object* v___x_5287_; lean_object* v_traceState_5288_; lean_object* v_traces_5289_; lean_object* v_ref_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; size_t v_sz_5293_; size_t v___x_5294_; lean_object* v___x_5295_; lean_object* v_msg_5296_; lean_object* v___x_5297_; lean_object* v_a_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5335_; 
v_fileName_5271_ = lean_ctor_get(v___y_5268_, 0);
v_fileMap_5272_ = lean_ctor_get(v___y_5268_, 1);
v_options_5273_ = lean_ctor_get(v___y_5268_, 2);
v_currRecDepth_5274_ = lean_ctor_get(v___y_5268_, 3);
v_maxRecDepth_5275_ = lean_ctor_get(v___y_5268_, 4);
v_ref_5276_ = lean_ctor_get(v___y_5268_, 5);
v_currNamespace_5277_ = lean_ctor_get(v___y_5268_, 6);
v_openDecls_5278_ = lean_ctor_get(v___y_5268_, 7);
v_initHeartbeats_5279_ = lean_ctor_get(v___y_5268_, 8);
v_maxHeartbeats_5280_ = lean_ctor_get(v___y_5268_, 9);
v_quotContext_5281_ = lean_ctor_get(v___y_5268_, 10);
v_currMacroScope_5282_ = lean_ctor_get(v___y_5268_, 11);
v_diag_5283_ = lean_ctor_get_uint8(v___y_5268_, sizeof(void*)*14);
v_cancelTk_x3f_5284_ = lean_ctor_get(v___y_5268_, 12);
v_suppressElabErrors_5285_ = lean_ctor_get_uint8(v___y_5268_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5286_ = lean_ctor_get(v___y_5268_, 13);
v___x_5287_ = lean_st_ref_get(v___y_5269_);
v_traceState_5288_ = lean_ctor_get(v___x_5287_, 4);
lean_inc_ref(v_traceState_5288_);
lean_dec(v___x_5287_);
v_traces_5289_ = lean_ctor_get(v_traceState_5288_, 0);
lean_inc_ref(v_traces_5289_);
lean_dec_ref(v_traceState_5288_);
v_ref_5290_ = l_Lean_replaceRef(v_ref_5264_, v_ref_5276_);
lean_inc_ref(v_inheritedTraceOptions_5286_);
lean_inc(v_cancelTk_x3f_5284_);
lean_inc(v_currMacroScope_5282_);
lean_inc(v_quotContext_5281_);
lean_inc(v_maxHeartbeats_5280_);
lean_inc(v_initHeartbeats_5279_);
lean_inc(v_openDecls_5278_);
lean_inc(v_currNamespace_5277_);
lean_inc(v_maxRecDepth_5275_);
lean_inc(v_currRecDepth_5274_);
lean_inc_ref(v_options_5273_);
lean_inc_ref(v_fileMap_5272_);
lean_inc_ref(v_fileName_5271_);
v___x_5291_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5291_, 0, v_fileName_5271_);
lean_ctor_set(v___x_5291_, 1, v_fileMap_5272_);
lean_ctor_set(v___x_5291_, 2, v_options_5273_);
lean_ctor_set(v___x_5291_, 3, v_currRecDepth_5274_);
lean_ctor_set(v___x_5291_, 4, v_maxRecDepth_5275_);
lean_ctor_set(v___x_5291_, 5, v_ref_5290_);
lean_ctor_set(v___x_5291_, 6, v_currNamespace_5277_);
lean_ctor_set(v___x_5291_, 7, v_openDecls_5278_);
lean_ctor_set(v___x_5291_, 8, v_initHeartbeats_5279_);
lean_ctor_set(v___x_5291_, 9, v_maxHeartbeats_5280_);
lean_ctor_set(v___x_5291_, 10, v_quotContext_5281_);
lean_ctor_set(v___x_5291_, 11, v_currMacroScope_5282_);
lean_ctor_set(v___x_5291_, 12, v_cancelTk_x3f_5284_);
lean_ctor_set(v___x_5291_, 13, v_inheritedTraceOptions_5286_);
lean_ctor_set_uint8(v___x_5291_, sizeof(void*)*14, v_diag_5283_);
lean_ctor_set_uint8(v___x_5291_, sizeof(void*)*14 + 1, v_suppressElabErrors_5285_);
v___x_5292_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5289_);
lean_dec_ref(v_traces_5289_);
v_sz_5293_ = lean_array_size(v___x_5292_);
v___x_5294_ = ((size_t)0ULL);
v___x_5295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3_spec__4(v_sz_5293_, v___x_5294_, v___x_5292_);
v_msg_5296_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5296_, 0, v_data_5263_);
lean_ctor_set(v_msg_5296_, 1, v_msg_5265_);
lean_ctor_set(v_msg_5296_, 2, v___x_5295_);
v___x_5297_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0_spec__0(v_msg_5296_, v___y_5266_, v___y_5267_, v___x_5291_, v___y_5269_);
lean_dec_ref_known(v___x_5291_, 14);
v_a_5298_ = lean_ctor_get(v___x_5297_, 0);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5297_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5300_ = v___x_5297_;
v_isShared_5301_ = v_isSharedCheck_5335_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_a_5298_);
lean_dec(v___x_5297_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5335_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5302_; lean_object* v_traceState_5303_; lean_object* v_env_5304_; lean_object* v_nextMacroScope_5305_; lean_object* v_ngen_5306_; lean_object* v_auxDeclNGen_5307_; lean_object* v_cache_5308_; lean_object* v_messages_5309_; lean_object* v_infoState_5310_; lean_object* v_snapshotTasks_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5334_; 
v___x_5302_ = lean_st_ref_take(v___y_5269_);
v_traceState_5303_ = lean_ctor_get(v___x_5302_, 4);
v_env_5304_ = lean_ctor_get(v___x_5302_, 0);
v_nextMacroScope_5305_ = lean_ctor_get(v___x_5302_, 1);
v_ngen_5306_ = lean_ctor_get(v___x_5302_, 2);
v_auxDeclNGen_5307_ = lean_ctor_get(v___x_5302_, 3);
v_cache_5308_ = lean_ctor_get(v___x_5302_, 5);
v_messages_5309_ = lean_ctor_get(v___x_5302_, 6);
v_infoState_5310_ = lean_ctor_get(v___x_5302_, 7);
v_snapshotTasks_5311_ = lean_ctor_get(v___x_5302_, 8);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5302_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5313_ = v___x_5302_;
v_isShared_5314_ = v_isSharedCheck_5334_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_snapshotTasks_5311_);
lean_inc(v_infoState_5310_);
lean_inc(v_messages_5309_);
lean_inc(v_cache_5308_);
lean_inc(v_traceState_5303_);
lean_inc(v_auxDeclNGen_5307_);
lean_inc(v_ngen_5306_);
lean_inc(v_nextMacroScope_5305_);
lean_inc(v_env_5304_);
lean_dec(v___x_5302_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5334_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
uint64_t v_tid_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5332_; 
v_tid_5315_ = lean_ctor_get_uint64(v_traceState_5303_, sizeof(void*)*1);
v_isSharedCheck_5332_ = !lean_is_exclusive(v_traceState_5303_);
if (v_isSharedCheck_5332_ == 0)
{
lean_object* v_unused_5333_; 
v_unused_5333_ = lean_ctor_get(v_traceState_5303_, 0);
lean_dec(v_unused_5333_);
v___x_5317_ = v_traceState_5303_;
v_isShared_5318_ = v_isSharedCheck_5332_;
goto v_resetjp_5316_;
}
else
{
lean_dec(v_traceState_5303_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5332_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5322_; 
v___x_5319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5319_, 0, v_ref_5264_);
lean_ctor_set(v___x_5319_, 1, v_a_5298_);
v___x_5320_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5262_, v___x_5319_);
if (v_isShared_5318_ == 0)
{
lean_ctor_set(v___x_5317_, 0, v___x_5320_);
v___x_5322_ = v___x_5317_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v___x_5320_);
lean_ctor_set_uint64(v_reuseFailAlloc_5331_, sizeof(void*)*1, v_tid_5315_);
v___x_5322_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
lean_object* v___x_5324_; 
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 4, v___x_5322_);
v___x_5324_ = v___x_5313_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_env_5304_);
lean_ctor_set(v_reuseFailAlloc_5330_, 1, v_nextMacroScope_5305_);
lean_ctor_set(v_reuseFailAlloc_5330_, 2, v_ngen_5306_);
lean_ctor_set(v_reuseFailAlloc_5330_, 3, v_auxDeclNGen_5307_);
lean_ctor_set(v_reuseFailAlloc_5330_, 4, v___x_5322_);
lean_ctor_set(v_reuseFailAlloc_5330_, 5, v_cache_5308_);
lean_ctor_set(v_reuseFailAlloc_5330_, 6, v_messages_5309_);
lean_ctor_set(v_reuseFailAlloc_5330_, 7, v_infoState_5310_);
lean_ctor_set(v_reuseFailAlloc_5330_, 8, v_snapshotTasks_5311_);
v___x_5324_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5328_; 
v___x_5325_ = lean_st_ref_set(v___y_5269_, v___x_5324_);
v___x_5326_ = lean_box(0);
if (v_isShared_5301_ == 0)
{
lean_ctor_set(v___x_5300_, 0, v___x_5326_);
v___x_5328_ = v___x_5300_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v___x_5326_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_5336_, lean_object* v_data_5337_, lean_object* v_ref_5338_, lean_object* v_msg_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_){
_start:
{
lean_object* v_res_5345_; 
v_res_5345_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_5336_, v_data_5337_, v_ref_5338_, v_msg_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_);
lean_dec(v___y_5343_);
lean_dec_ref(v___y_5342_);
lean_dec(v___y_5341_);
lean_dec_ref(v___y_5340_);
return v_res_5345_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1(void){
_start:
{
lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5347_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__0));
v___x_5348_ = l_Lean_stringToMessageData(v___x_5347_);
return v___x_5348_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2(void){
_start:
{
lean_object* v___x_5349_; double v___x_5350_; 
v___x_5349_ = lean_unsigned_to_nat(1000u);
v___x_5350_ = lean_float_of_nat(v___x_5349_);
return v___x_5350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(lean_object* v_cls_5351_, uint8_t v_collapsed_5352_, lean_object* v_tag_5353_, lean_object* v_opts_5354_, uint8_t v_clsEnabled_5355_, lean_object* v_oldTraces_5356_, lean_object* v_msg_5357_, lean_object* v_resStartStop_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_){
_start:
{
lean_object* v_fst_5368_; lean_object* v_snd_5369_; lean_object* v___y_5371_; lean_object* v___y_5372_; lean_object* v_data_5373_; lean_object* v_fst_5384_; lean_object* v_snd_5385_; lean_object* v___x_5386_; uint8_t v___x_5387_; lean_object* v___y_5389_; lean_object* v_a_5390_; uint8_t v___y_5405_; double v___y_5436_; 
v_fst_5368_ = lean_ctor_get(v_resStartStop_5358_, 0);
lean_inc(v_fst_5368_);
v_snd_5369_ = lean_ctor_get(v_resStartStop_5358_, 1);
lean_inc(v_snd_5369_);
lean_dec_ref(v_resStartStop_5358_);
v_fst_5384_ = lean_ctor_get(v_snd_5369_, 0);
lean_inc(v_fst_5384_);
v_snd_5385_ = lean_ctor_get(v_snd_5369_, 1);
lean_inc(v_snd_5385_);
lean_dec(v_snd_5369_);
v___x_5386_ = l_Lean_trace_profiler;
v___x_5387_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_5354_, v___x_5386_);
if (v___x_5387_ == 0)
{
v___y_5405_ = v___x_5387_;
goto v___jp_5404_;
}
else
{
lean_object* v___x_5441_; uint8_t v___x_5442_; 
v___x_5441_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5442_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_opts_5354_, v___x_5441_);
if (v___x_5442_ == 0)
{
lean_object* v___x_5443_; lean_object* v___x_5444_; double v___x_5445_; double v___x_5446_; double v___x_5447_; 
v___x_5443_ = l_Lean_trace_profiler_threshold;
v___x_5444_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_5354_, v___x_5443_);
v___x_5445_ = lean_float_of_nat(v___x_5444_);
v___x_5446_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__2);
v___x_5447_ = lean_float_div(v___x_5445_, v___x_5446_);
v___y_5436_ = v___x_5447_;
goto v___jp_5435_;
}
else
{
lean_object* v___x_5448_; lean_object* v___x_5449_; double v___x_5450_; 
v___x_5448_ = l_Lean_trace_profiler_threshold;
v___x_5449_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__6(v_opts_5354_, v___x_5448_);
v___x_5450_ = lean_float_of_nat(v___x_5449_);
v___y_5436_ = v___x_5450_;
goto v___jp_5435_;
}
}
v___jp_5370_:
{
lean_object* v___x_5374_; 
lean_inc(v___y_5372_);
v___x_5374_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_5356_, v_data_5373_, v___y_5372_, v___y_5371_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_);
if (lean_obj_tag(v___x_5374_) == 0)
{
lean_object* v___x_5375_; 
lean_dec_ref_known(v___x_5374_, 1);
v___x_5375_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_5368_);
return v___x_5375_;
}
else
{
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5383_; 
lean_dec(v_fst_5368_);
v_a_5376_ = lean_ctor_get(v___x_5374_, 0);
v_isSharedCheck_5383_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5383_ == 0)
{
v___x_5378_ = v___x_5374_;
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v___x_5374_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5381_; 
if (v_isShared_5379_ == 0)
{
v___x_5381_ = v___x_5378_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_a_5376_);
v___x_5381_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
return v___x_5381_;
}
}
}
}
v___jp_5388_:
{
uint8_t v_result_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; double v___x_5394_; lean_object* v_data_5395_; 
v_result_5391_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__5(v_fst_5368_);
v___x_5392_ = lean_box(v_result_5391_);
v___x_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5393_, 0, v___x_5392_);
v___x_5394_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_5353_);
lean_inc_ref(v___x_5393_);
lean_inc(v_cls_5351_);
v_data_5395_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5395_, 0, v_cls_5351_);
lean_ctor_set(v_data_5395_, 1, v___x_5393_);
lean_ctor_set(v_data_5395_, 2, v_tag_5353_);
lean_ctor_set_float(v_data_5395_, sizeof(void*)*3, v___x_5394_);
lean_ctor_set_float(v_data_5395_, sizeof(void*)*3 + 8, v___x_5394_);
lean_ctor_set_uint8(v_data_5395_, sizeof(void*)*3 + 16, v_collapsed_5352_);
if (v___x_5387_ == 0)
{
lean_dec_ref_known(v___x_5393_, 1);
lean_dec(v_snd_5385_);
lean_dec(v_fst_5384_);
lean_dec_ref(v_tag_5353_);
lean_dec(v_cls_5351_);
v___y_5371_ = v_a_5390_;
v___y_5372_ = v___y_5389_;
v_data_5373_ = v_data_5395_;
goto v___jp_5370_;
}
else
{
lean_object* v_data_5396_; double v___x_5397_; double v___x_5398_; 
lean_dec_ref_known(v_data_5395_, 3);
v_data_5396_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5396_, 0, v_cls_5351_);
lean_ctor_set(v_data_5396_, 1, v___x_5393_);
lean_ctor_set(v_data_5396_, 2, v_tag_5353_);
v___x_5397_ = lean_unbox_float(v_fst_5384_);
lean_dec(v_fst_5384_);
lean_ctor_set_float(v_data_5396_, sizeof(void*)*3, v___x_5397_);
v___x_5398_ = lean_unbox_float(v_snd_5385_);
lean_dec(v_snd_5385_);
lean_ctor_set_float(v_data_5396_, sizeof(void*)*3 + 8, v___x_5398_);
lean_ctor_set_uint8(v_data_5396_, sizeof(void*)*3 + 16, v_collapsed_5352_);
v___y_5371_ = v_a_5390_;
v___y_5372_ = v___y_5389_;
v_data_5373_ = v_data_5396_;
goto v___jp_5370_;
}
}
v___jp_5399_:
{
lean_object* v_ref_5400_; lean_object* v___x_5401_; 
v_ref_5400_ = lean_ctor_get(v___y_5365_, 5);
lean_inc(v___y_5366_);
lean_inc_ref(v___y_5365_);
lean_inc(v___y_5364_);
lean_inc_ref(v___y_5363_);
lean_inc(v___y_5362_);
lean_inc_ref(v___y_5361_);
lean_inc(v___y_5360_);
lean_inc_ref(v___y_5359_);
lean_inc(v_fst_5368_);
v___x_5401_ = lean_apply_10(v_msg_5357_, v_fst_5368_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_, lean_box(0));
if (lean_obj_tag(v___x_5401_) == 0)
{
lean_object* v_a_5402_; 
v_a_5402_ = lean_ctor_get(v___x_5401_, 0);
lean_inc(v_a_5402_);
lean_dec_ref_known(v___x_5401_, 1);
v___y_5389_ = v_ref_5400_;
v_a_5390_ = v_a_5402_;
goto v___jp_5388_;
}
else
{
lean_object* v___x_5403_; 
lean_dec_ref_known(v___x_5401_, 1);
v___x_5403_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___closed__1);
v___y_5389_ = v_ref_5400_;
v_a_5390_ = v___x_5403_;
goto v___jp_5388_;
}
}
v___jp_5404_:
{
if (v_clsEnabled_5355_ == 0)
{
if (v___y_5405_ == 0)
{
lean_object* v___x_5406_; lean_object* v_traceState_5407_; lean_object* v_env_5408_; lean_object* v_nextMacroScope_5409_; lean_object* v_ngen_5410_; lean_object* v_auxDeclNGen_5411_; lean_object* v_cache_5412_; lean_object* v_messages_5413_; lean_object* v_infoState_5414_; lean_object* v_snapshotTasks_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5434_; 
lean_dec(v_snd_5385_);
lean_dec(v_fst_5384_);
lean_dec_ref(v_msg_5357_);
lean_dec_ref(v_tag_5353_);
lean_dec(v_cls_5351_);
v___x_5406_ = lean_st_ref_take(v___y_5366_);
v_traceState_5407_ = lean_ctor_get(v___x_5406_, 4);
v_env_5408_ = lean_ctor_get(v___x_5406_, 0);
v_nextMacroScope_5409_ = lean_ctor_get(v___x_5406_, 1);
v_ngen_5410_ = lean_ctor_get(v___x_5406_, 2);
v_auxDeclNGen_5411_ = lean_ctor_get(v___x_5406_, 3);
v_cache_5412_ = lean_ctor_get(v___x_5406_, 5);
v_messages_5413_ = lean_ctor_get(v___x_5406_, 6);
v_infoState_5414_ = lean_ctor_get(v___x_5406_, 7);
v_snapshotTasks_5415_ = lean_ctor_get(v___x_5406_, 8);
v_isSharedCheck_5434_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5434_ == 0)
{
v___x_5417_ = v___x_5406_;
v_isShared_5418_ = v_isSharedCheck_5434_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_snapshotTasks_5415_);
lean_inc(v_infoState_5414_);
lean_inc(v_messages_5413_);
lean_inc(v_cache_5412_);
lean_inc(v_traceState_5407_);
lean_inc(v_auxDeclNGen_5411_);
lean_inc(v_ngen_5410_);
lean_inc(v_nextMacroScope_5409_);
lean_inc(v_env_5408_);
lean_dec(v___x_5406_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5434_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
uint64_t v_tid_5419_; lean_object* v_traces_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5433_; 
v_tid_5419_ = lean_ctor_get_uint64(v_traceState_5407_, sizeof(void*)*1);
v_traces_5420_ = lean_ctor_get(v_traceState_5407_, 0);
v_isSharedCheck_5433_ = !lean_is_exclusive(v_traceState_5407_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5422_ = v_traceState_5407_;
v_isShared_5423_ = v_isSharedCheck_5433_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_traces_5420_);
lean_dec(v_traceState_5407_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5433_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5424_; lean_object* v___x_5426_; 
v___x_5424_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5356_, v_traces_5420_);
lean_dec_ref(v_traces_5420_);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 0, v___x_5424_);
v___x_5426_ = v___x_5422_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v___x_5424_);
lean_ctor_set_uint64(v_reuseFailAlloc_5432_, sizeof(void*)*1, v_tid_5419_);
v___x_5426_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
lean_object* v___x_5428_; 
if (v_isShared_5418_ == 0)
{
lean_ctor_set(v___x_5417_, 4, v___x_5426_);
v___x_5428_ = v___x_5417_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_env_5408_);
lean_ctor_set(v_reuseFailAlloc_5431_, 1, v_nextMacroScope_5409_);
lean_ctor_set(v_reuseFailAlloc_5431_, 2, v_ngen_5410_);
lean_ctor_set(v_reuseFailAlloc_5431_, 3, v_auxDeclNGen_5411_);
lean_ctor_set(v_reuseFailAlloc_5431_, 4, v___x_5426_);
lean_ctor_set(v_reuseFailAlloc_5431_, 5, v_cache_5412_);
lean_ctor_set(v_reuseFailAlloc_5431_, 6, v_messages_5413_);
lean_ctor_set(v_reuseFailAlloc_5431_, 7, v_infoState_5414_);
lean_ctor_set(v_reuseFailAlloc_5431_, 8, v_snapshotTasks_5415_);
v___x_5428_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___x_5429_ = lean_st_ref_set(v___y_5366_, v___x_5428_);
v___x_5430_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_fst_5368_);
return v___x_5430_;
}
}
}
}
}
else
{
goto v___jp_5399_;
}
}
else
{
goto v___jp_5399_;
}
}
v___jp_5435_:
{
double v___x_5437_; double v___x_5438_; double v___x_5439_; uint8_t v___x_5440_; 
v___x_5437_ = lean_unbox_float(v_snd_5385_);
v___x_5438_ = lean_unbox_float(v_fst_5384_);
v___x_5439_ = lean_float_sub(v___x_5437_, v___x_5438_);
v___x_5440_ = lean_float_decLt(v___y_5436_, v___x_5439_);
v___y_5405_ = v___x_5440_;
goto v___jp_5404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3___boxed(lean_object** _args){
lean_object* v_cls_5451_ = _args[0];
lean_object* v_collapsed_5452_ = _args[1];
lean_object* v_tag_5453_ = _args[2];
lean_object* v_opts_5454_ = _args[3];
lean_object* v_clsEnabled_5455_ = _args[4];
lean_object* v_oldTraces_5456_ = _args[5];
lean_object* v_msg_5457_ = _args[6];
lean_object* v_resStartStop_5458_ = _args[7];
lean_object* v___y_5459_ = _args[8];
lean_object* v___y_5460_ = _args[9];
lean_object* v___y_5461_ = _args[10];
lean_object* v___y_5462_ = _args[11];
lean_object* v___y_5463_ = _args[12];
lean_object* v___y_5464_ = _args[13];
lean_object* v___y_5465_ = _args[14];
lean_object* v___y_5466_ = _args[15];
lean_object* v___y_5467_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_5468_; uint8_t v_clsEnabled_boxed_5469_; lean_object* v_res_5470_; 
v_collapsed_boxed_5468_ = lean_unbox(v_collapsed_5452_);
v_clsEnabled_boxed_5469_ = lean_unbox(v_clsEnabled_5455_);
v_res_5470_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v_cls_5451_, v_collapsed_boxed_5468_, v_tag_5453_, v_opts_5454_, v_clsEnabled_boxed_5469_, v_oldTraces_5456_, v_msg_5457_, v_resStartStop_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_);
lean_dec(v___y_5466_);
lean_dec_ref(v___y_5465_);
lean_dec(v___y_5464_);
lean_dec_ref(v___y_5463_);
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
lean_dec_ref(v_opts_5454_);
return v_res_5470_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_5475_; lean_object* v___x_5476_; 
v___x_5475_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__1));
v___x_5476_ = l_Lean_stringToMessageData(v___x_5475_);
return v___x_5476_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(lean_object* v_as_x27_5477_, lean_object* v_b_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_){
_start:
{
if (lean_obj_tag(v_as_x27_5477_) == 0)
{
lean_object* v___x_5488_; 
v___x_5488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5488_, 0, v_b_5478_);
return v___x_5488_;
}
else
{
lean_object* v_head_5489_; lean_object* v_options_5490_; lean_object* v_tail_5491_; lean_object* v_name_5492_; lean_object* v_run_x27_5493_; lean_object* v_inheritedTraceOptions_5494_; uint8_t v_hasTrace_5495_; lean_object* v___x_5496_; uint8_t v___y_5498_; lean_object* v___x_5503_; lean_object* v___y_5505_; 
lean_dec_ref(v_b_5478_);
v_head_5489_ = lean_ctor_get(v_as_x27_5477_, 0);
v_options_5490_ = lean_ctor_get(v___y_5485_, 2);
v_tail_5491_ = lean_ctor_get(v_as_x27_5477_, 1);
v_name_5492_ = lean_ctor_get(v_head_5489_, 0);
v_run_x27_5493_ = lean_ctor_get(v_head_5489_, 1);
v_inheritedTraceOptions_5494_ = lean_ctor_get(v___y_5485_, 13);
v_hasTrace_5495_ = lean_ctor_get_uint8(v_options_5490_, sizeof(void*)*1);
v___x_5496_ = lean_box(0);
v___x_5503_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
if (v_hasTrace_5495_ == 0)
{
lean_object* v___x_5533_; 
lean_inc_ref(v_run_x27_5493_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
lean_inc(v___y_5482_);
lean_inc_ref(v___y_5481_);
lean_inc(v___y_5480_);
lean_inc_ref(v___y_5479_);
v___x_5533_ = lean_apply_9(v_run_x27_5493_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, lean_box(0));
v___y_5505_ = v___x_5533_;
goto v___jp_5504_;
}
else
{
lean_object* v___f_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; uint8_t v___x_5538_; lean_object* v___y_5540_; lean_object* v___y_5541_; lean_object* v_a_5542_; lean_object* v___y_5555_; lean_object* v___y_5556_; lean_object* v_a_5557_; 
lean_inc(v_name_5492_);
v___f_5534_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5534_, 0, v_name_5492_);
v___x_5535_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_5536_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps_go_spec__0___redArg___closed__1));
v___x_5537_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_5538_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5494_, v_options_5490_, v___x_5537_);
if (v___x_5538_ == 0)
{
lean_object* v___x_5607_; uint8_t v___x_5608_; 
v___x_5607_ = l_Lean_trace_profiler;
v___x_5608_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_5490_, v___x_5607_);
if (v___x_5608_ == 0)
{
lean_object* v___x_5609_; 
lean_dec_ref(v___f_5534_);
lean_inc_ref(v_run_x27_5493_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
lean_inc(v___y_5482_);
lean_inc_ref(v___y_5481_);
lean_inc(v___y_5480_);
lean_inc_ref(v___y_5479_);
v___x_5609_ = lean_apply_9(v_run_x27_5493_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, lean_box(0));
v___y_5505_ = v___x_5609_;
goto v___jp_5504_;
}
else
{
goto v___jp_5566_;
}
}
else
{
goto v___jp_5566_;
}
v___jp_5539_:
{
lean_object* v___x_5543_; double v___x_5544_; double v___x_5545_; double v___x_5546_; double v___x_5547_; double v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; 
v___x_5543_ = lean_io_mono_nanos_now();
v___x_5544_ = lean_float_of_nat(v___y_5540_);
v___x_5545_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10);
v___x_5546_ = lean_float_div(v___x_5544_, v___x_5545_);
v___x_5547_ = lean_float_of_nat(v___x_5543_);
v___x_5548_ = lean_float_div(v___x_5547_, v___x_5545_);
v___x_5549_ = lean_box_float(v___x_5546_);
v___x_5550_ = lean_box_float(v___x_5548_);
v___x_5551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5551_, 0, v___x_5549_);
lean_ctor_set(v___x_5551_, 1, v___x_5550_);
v___x_5552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5552_, 0, v_a_5542_);
lean_ctor_set(v___x_5552_, 1, v___x_5551_);
v___x_5553_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_5535_, v_hasTrace_5495_, v___x_5536_, v_options_5490_, v___x_5538_, v___y_5541_, v___f_5534_, v___x_5552_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
v___y_5505_ = v___x_5553_;
goto v___jp_5504_;
}
v___jp_5554_:
{
lean_object* v___x_5558_; double v___x_5559_; double v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; 
v___x_5558_ = lean_io_get_num_heartbeats();
v___x_5559_ = lean_float_of_nat(v___y_5555_);
v___x_5560_ = lean_float_of_nat(v___x_5558_);
v___x_5561_ = lean_box_float(v___x_5559_);
v___x_5562_ = lean_box_float(v___x_5560_);
v___x_5563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5563_, 0, v___x_5561_);
lean_ctor_set(v___x_5563_, 1, v___x_5562_);
v___x_5564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5564_, 0, v_a_5557_);
lean_ctor_set(v___x_5564_, 1, v___x_5563_);
v___x_5565_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3(v___x_5535_, v_hasTrace_5495_, v___x_5536_, v_options_5490_, v___x_5538_, v___y_5556_, v___f_5534_, v___x_5564_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
v___y_5505_ = v___x_5565_;
goto v___jp_5504_;
}
v___jp_5566_:
{
lean_object* v___x_5567_; lean_object* v_a_5568_; lean_object* v___x_5569_; uint8_t v___x_5570_; 
v___x_5567_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__1___redArg(v___y_5486_);
v_a_5568_ = lean_ctor_get(v___x_5567_, 0);
lean_inc(v_a_5568_);
lean_dec_ref(v___x_5567_);
v___x_5569_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5570_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__2(v_options_5490_, v___x_5569_);
if (v___x_5570_ == 0)
{
lean_object* v___x_5571_; lean_object* v___x_5572_; 
v___x_5571_ = lean_io_mono_nanos_now();
lean_inc_ref(v_run_x27_5493_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
lean_inc(v___y_5482_);
lean_inc_ref(v___y_5481_);
lean_inc(v___y_5480_);
lean_inc_ref(v___y_5479_);
v___x_5572_ = lean_apply_9(v_run_x27_5493_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, lean_box(0));
if (lean_obj_tag(v___x_5572_) == 0)
{
lean_object* v_a_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5580_; 
v_a_5573_ = lean_ctor_get(v___x_5572_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5575_ = v___x_5572_;
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_a_5573_);
lean_dec(v___x_5572_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___x_5578_; 
if (v_isShared_5576_ == 0)
{
lean_ctor_set_tag(v___x_5575_, 1);
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
v___y_5540_ = v___x_5571_;
v___y_5541_ = v_a_5568_;
v_a_5542_ = v___x_5578_;
goto v___jp_5539_;
}
}
}
else
{
lean_object* v_a_5581_; lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5588_; 
v_a_5581_ = lean_ctor_get(v___x_5572_, 0);
v_isSharedCheck_5588_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5588_ == 0)
{
v___x_5583_ = v___x_5572_;
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_a_5581_);
lean_dec(v___x_5572_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v___x_5586_; 
if (v_isShared_5584_ == 0)
{
lean_ctor_set_tag(v___x_5583_, 0);
v___x_5586_ = v___x_5583_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_a_5581_);
v___x_5586_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
v___y_5540_ = v___x_5571_;
v___y_5541_ = v_a_5568_;
v_a_5542_ = v___x_5586_;
goto v___jp_5539_;
}
}
}
}
else
{
lean_object* v___x_5589_; lean_object* v___x_5590_; 
v___x_5589_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_run_x27_5493_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
lean_inc(v___y_5484_);
lean_inc_ref(v___y_5483_);
lean_inc(v___y_5482_);
lean_inc_ref(v___y_5481_);
lean_inc(v___y_5480_);
lean_inc_ref(v___y_5479_);
v___x_5590_ = lean_apply_9(v_run_x27_5493_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, lean_box(0));
if (lean_obj_tag(v___x_5590_) == 0)
{
lean_object* v_a_5591_; lean_object* v___x_5593_; uint8_t v_isShared_5594_; uint8_t v_isSharedCheck_5598_; 
v_a_5591_ = lean_ctor_get(v___x_5590_, 0);
v_isSharedCheck_5598_ = !lean_is_exclusive(v___x_5590_);
if (v_isSharedCheck_5598_ == 0)
{
v___x_5593_ = v___x_5590_;
v_isShared_5594_ = v_isSharedCheck_5598_;
goto v_resetjp_5592_;
}
else
{
lean_inc(v_a_5591_);
lean_dec(v___x_5590_);
v___x_5593_ = lean_box(0);
v_isShared_5594_ = v_isSharedCheck_5598_;
goto v_resetjp_5592_;
}
v_resetjp_5592_:
{
lean_object* v___x_5596_; 
if (v_isShared_5594_ == 0)
{
lean_ctor_set_tag(v___x_5593_, 1);
v___x_5596_ = v___x_5593_;
goto v_reusejp_5595_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_a_5591_);
v___x_5596_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5595_;
}
v_reusejp_5595_:
{
v___y_5555_ = v___x_5589_;
v___y_5556_ = v_a_5568_;
v_a_5557_ = v___x_5596_;
goto v___jp_5554_;
}
}
}
else
{
lean_object* v_a_5599_; lean_object* v___x_5601_; uint8_t v_isShared_5602_; uint8_t v_isSharedCheck_5606_; 
v_a_5599_ = lean_ctor_get(v___x_5590_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5590_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5601_ = v___x_5590_;
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
else
{
lean_inc(v_a_5599_);
lean_dec(v___x_5590_);
v___x_5601_ = lean_box(0);
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
v_resetjp_5600_:
{
lean_object* v___x_5604_; 
if (v_isShared_5602_ == 0)
{
lean_ctor_set_tag(v___x_5601_, 0);
v___x_5604_ = v___x_5601_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_a_5599_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
v___y_5555_ = v___x_5589_;
v___y_5556_ = v_a_5568_;
v_a_5557_ = v___x_5604_;
goto v___jp_5554_;
}
}
}
}
}
}
v___jp_5497_:
{
lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; 
v___x_5499_ = lean_box(v___y_5498_);
v___x_5500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5500_, 0, v___x_5499_);
v___x_5501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5501_, 0, v___x_5500_);
lean_ctor_set(v___x_5501_, 1, v___x_5496_);
v___x_5502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5502_, 0, v___x_5501_);
return v___x_5502_;
}
v___jp_5504_:
{
if (lean_obj_tag(v___y_5505_) == 0)
{
lean_object* v_a_5506_; uint8_t v___x_5507_; 
v_a_5506_ = lean_ctor_get(v___y_5505_, 0);
lean_inc(v_a_5506_);
lean_dec_ref_known(v___y_5505_, 1);
v___x_5507_ = lean_unbox(v_a_5506_);
if (v___x_5507_ == 0)
{
lean_dec(v_a_5506_);
v_as_x27_5477_ = v_tail_5491_;
v_b_5478_ = v___x_5503_;
goto _start;
}
else
{
if (v_hasTrace_5495_ == 0)
{
uint8_t v___x_5509_; 
v___x_5509_ = lean_unbox(v_a_5506_);
lean_dec(v_a_5506_);
v___y_5498_ = v___x_5509_;
goto v___jp_5497_;
}
else
{
lean_object* v___x_5510_; lean_object* v___x_5511_; uint8_t v___x_5512_; 
v___x_5510_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_5511_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_5512_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5494_, v_options_5490_, v___x_5511_);
if (v___x_5512_ == 0)
{
uint8_t v___x_5513_; 
v___x_5513_ = lean_unbox(v_a_5506_);
lean_dec(v_a_5506_);
v___y_5498_ = v___x_5513_;
goto v___jp_5497_;
}
else
{
lean_object* v___x_5514_; lean_object* v___x_5515_; 
v___x_5514_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__2);
v___x_5515_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_5510_, v___x_5514_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
if (lean_obj_tag(v___x_5515_) == 0)
{
uint8_t v___x_5516_; 
lean_dec_ref_known(v___x_5515_, 1);
v___x_5516_ = lean_unbox(v_a_5506_);
lean_dec(v_a_5506_);
v___y_5498_ = v___x_5516_;
goto v___jp_5497_;
}
else
{
lean_object* v_a_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5524_; 
lean_dec(v_a_5506_);
v_a_5517_ = lean_ctor_get(v___x_5515_, 0);
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5515_);
if (v_isSharedCheck_5524_ == 0)
{
v___x_5519_ = v___x_5515_;
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_a_5517_);
lean_dec(v___x_5515_);
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
}
}
}
else
{
lean_object* v_a_5525_; lean_object* v___x_5527_; uint8_t v_isShared_5528_; uint8_t v_isSharedCheck_5532_; 
v_a_5525_ = lean_ctor_get(v___y_5505_, 0);
v_isSharedCheck_5532_ = !lean_is_exclusive(v___y_5505_);
if (v_isSharedCheck_5532_ == 0)
{
v___x_5527_ = v___y_5505_;
v_isShared_5528_ = v_isSharedCheck_5532_;
goto v_resetjp_5526_;
}
else
{
lean_inc(v_a_5525_);
lean_dec(v___y_5505_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___boxed(lean_object* v_as_x27_5610_, lean_object* v_b_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_){
_start:
{
lean_object* v_res_5621_; 
v_res_5621_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_5610_, v_b_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
lean_dec(v___y_5619_);
lean_dec_ref(v___y_5618_);
lean_dec(v___y_5617_);
lean_dec_ref(v___y_5616_);
lean_dec(v___y_5615_);
lean_dec_ref(v___y_5614_);
lean_dec(v___y_5613_);
lean_dec_ref(v___y_5612_);
lean_dec(v_as_x27_5610_);
return v_res_5621_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2(void){
_start:
{
lean_object* v___x_5624_; lean_object* v___x_5625_; 
v___x_5624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__1));
v___x_5625_ = l_Lean_stringToMessageData(v___x_5624_);
return v___x_5625_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4(void){
_start:
{
lean_object* v___x_5627_; lean_object* v___x_5628_; 
v___x_5627_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__3));
v___x_5628_ = l_Lean_stringToMessageData(v___x_5627_);
return v___x_5628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(lean_object* v_passes_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_){
_start:
{
lean_object* v___x_5639_; lean_object* v___x_5640_; 
v___x_5639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__0));
v___x_5640_ = l_Lean_Core_checkSystem(v___x_5639_, v_a_5636_, v_a_5637_);
if (lean_obj_tag(v___x_5640_) == 0)
{
lean_object* v___x_5641_; lean_object* v_rewriteSimpCache_5642_; lean_object* v_rewriteDSimpCache_5643_; lean_object* v_acCache_5644_; lean_object* v_typeAnalysis_5645_; lean_object* v_goal_5646_; lean_object* v_hypotheses_5647_; lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5730_; 
lean_dec_ref_known(v___x_5640_, 1);
v___x_5641_ = lean_st_ref_take(v_a_5631_);
v_rewriteSimpCache_5642_ = lean_ctor_get(v___x_5641_, 0);
v_rewriteDSimpCache_5643_ = lean_ctor_get(v___x_5641_, 1);
v_acCache_5644_ = lean_ctor_get(v___x_5641_, 2);
v_typeAnalysis_5645_ = lean_ctor_get(v___x_5641_, 3);
v_goal_5646_ = lean_ctor_get(v___x_5641_, 4);
v_hypotheses_5647_ = lean_ctor_get(v___x_5641_, 5);
v_isSharedCheck_5730_ = !lean_is_exclusive(v___x_5641_);
if (v_isSharedCheck_5730_ == 0)
{
v___x_5649_ = v___x_5641_;
v_isShared_5650_ = v_isSharedCheck_5730_;
goto v_resetjp_5648_;
}
else
{
lean_inc(v_hypotheses_5647_);
lean_inc(v_goal_5646_);
lean_inc(v_typeAnalysis_5645_);
lean_inc(v_acCache_5644_);
lean_inc(v_rewriteDSimpCache_5643_);
lean_inc(v_rewriteSimpCache_5642_);
lean_dec(v___x_5641_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5730_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
uint8_t v___x_5651_; lean_object* v___x_5653_; 
v___x_5651_ = 0;
if (v_isShared_5650_ == 0)
{
v___x_5653_ = v___x_5649_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5729_; 
v_reuseFailAlloc_5729_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5729_, 0, v_rewriteSimpCache_5642_);
lean_ctor_set(v_reuseFailAlloc_5729_, 1, v_rewriteDSimpCache_5643_);
lean_ctor_set(v_reuseFailAlloc_5729_, 2, v_acCache_5644_);
lean_ctor_set(v_reuseFailAlloc_5729_, 3, v_typeAnalysis_5645_);
lean_ctor_set(v_reuseFailAlloc_5729_, 4, v_goal_5646_);
lean_ctor_set(v_reuseFailAlloc_5729_, 5, v_hypotheses_5647_);
v___x_5653_ = v_reuseFailAlloc_5729_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; 
lean_ctor_set_uint8(v___x_5653_, sizeof(void*)*6, v___x_5651_);
v___x_5654_ = lean_st_ref_set(v_a_5631_, v___x_5653_);
v___x_5655_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg___closed__0));
v___x_5656_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_passes_5629_, v___x_5655_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_);
if (lean_obj_tag(v___x_5656_) == 0)
{
lean_object* v_a_5657_; lean_object* v___x_5659_; uint8_t v_isShared_5660_; uint8_t v_isSharedCheck_5720_; 
v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
v_isSharedCheck_5720_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5720_ == 0)
{
v___x_5659_ = v___x_5656_;
v_isShared_5660_ = v_isSharedCheck_5720_;
goto v_resetjp_5658_;
}
else
{
lean_inc(v_a_5657_);
lean_dec(v___x_5656_);
v___x_5659_ = lean_box(0);
v_isShared_5660_ = v_isSharedCheck_5720_;
goto v_resetjp_5658_;
}
v_resetjp_5658_:
{
lean_object* v_fst_5661_; 
v_fst_5661_ = lean_ctor_get(v_a_5657_, 0);
lean_inc(v_fst_5661_);
lean_dec(v_a_5657_);
if (lean_obj_tag(v_fst_5661_) == 0)
{
lean_object* v___x_5662_; uint8_t v_didChange_5663_; 
v___x_5662_ = lean_st_ref_get(v_a_5631_);
v_didChange_5663_ = lean_ctor_get_uint8(v___x_5662_, sizeof(void*)*6);
lean_dec(v___x_5662_);
if (v_didChange_5663_ == 0)
{
lean_object* v_options_5664_; uint8_t v_hasTrace_5665_; 
v_options_5664_ = lean_ctor_get(v_a_5636_, 2);
v_hasTrace_5665_ = lean_ctor_get_uint8(v_options_5664_, sizeof(void*)*1);
if (v_hasTrace_5665_ == 0)
{
lean_object* v___x_5666_; lean_object* v___x_5668_; 
v___x_5666_ = lean_box(v_didChange_5663_);
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 0, v___x_5666_);
v___x_5668_ = v___x_5659_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v___x_5666_);
v___x_5668_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
return v___x_5668_;
}
}
else
{
lean_object* v_inheritedTraceOptions_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; uint8_t v___x_5673_; 
v_inheritedTraceOptions_5670_ = lean_ctor_get(v_a_5636_, 13);
v___x_5671_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_5672_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_5673_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5670_, v_options_5664_, v___x_5672_);
if (v___x_5673_ == 0)
{
lean_object* v___x_5674_; lean_object* v___x_5676_; 
v___x_5674_ = lean_box(v_didChange_5663_);
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 0, v___x_5674_);
v___x_5676_ = v___x_5659_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v___x_5674_);
v___x_5676_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
return v___x_5676_;
}
}
else
{
lean_object* v___x_5678_; lean_object* v___x_5679_; 
lean_del_object(v___x_5659_);
v___x_5678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__2);
v___x_5679_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_5671_, v___x_5678_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_);
if (lean_obj_tag(v___x_5679_) == 0)
{
lean_object* v___x_5681_; uint8_t v_isShared_5682_; uint8_t v_isSharedCheck_5687_; 
v_isSharedCheck_5687_ = !lean_is_exclusive(v___x_5679_);
if (v_isSharedCheck_5687_ == 0)
{
lean_object* v_unused_5688_; 
v_unused_5688_ = lean_ctor_get(v___x_5679_, 0);
lean_dec(v_unused_5688_);
v___x_5681_ = v___x_5679_;
v_isShared_5682_ = v_isSharedCheck_5687_;
goto v_resetjp_5680_;
}
else
{
lean_dec(v___x_5679_);
v___x_5681_ = lean_box(0);
v_isShared_5682_ = v_isSharedCheck_5687_;
goto v_resetjp_5680_;
}
v_resetjp_5680_:
{
lean_object* v___x_5683_; lean_object* v___x_5685_; 
v___x_5683_ = lean_box(v_didChange_5663_);
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 0, v___x_5683_);
v___x_5685_ = v___x_5681_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v___x_5683_);
v___x_5685_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
return v___x_5685_;
}
}
}
else
{
lean_object* v_a_5689_; lean_object* v___x_5691_; uint8_t v_isShared_5692_; uint8_t v_isSharedCheck_5696_; 
v_a_5689_ = lean_ctor_get(v___x_5679_, 0);
v_isSharedCheck_5696_ = !lean_is_exclusive(v___x_5679_);
if (v_isSharedCheck_5696_ == 0)
{
v___x_5691_ = v___x_5679_;
v_isShared_5692_ = v_isSharedCheck_5696_;
goto v_resetjp_5690_;
}
else
{
lean_inc(v_a_5689_);
lean_dec(v___x_5679_);
v___x_5691_ = lean_box(0);
v_isShared_5692_ = v_isSharedCheck_5696_;
goto v_resetjp_5690_;
}
v_resetjp_5690_:
{
lean_object* v___x_5694_; 
if (v_isShared_5692_ == 0)
{
v___x_5694_ = v___x_5691_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v_a_5689_);
v___x_5694_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
return v___x_5694_;
}
}
}
}
}
}
else
{
lean_object* v_options_5697_; uint8_t v_hasTrace_5698_; 
lean_del_object(v___x_5659_);
v_options_5697_ = lean_ctor_get(v_a_5636_, 2);
v_hasTrace_5698_ = lean_ctor_get_uint8(v_options_5697_, sizeof(void*)*1);
if (v_hasTrace_5698_ == 0)
{
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; uint8_t v___x_5703_; 
v_inheritedTraceOptions_5700_ = lean_ctor_get(v_a_5636_, 13);
v___x_5701_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__17));
v___x_5702_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20, &l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_pushHyp___closed__20);
v___x_5703_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5700_, v_options_5697_, v___x_5702_);
if (v___x_5703_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_5705_; lean_object* v___x_5706_; 
v___x_5705_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___closed__4);
v___x_5706_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v___x_5701_, v___x_5705_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_);
if (lean_obj_tag(v___x_5706_) == 0)
{
lean_dec_ref_known(v___x_5706_, 1);
goto _start;
}
else
{
lean_object* v_a_5708_; lean_object* v___x_5710_; uint8_t v_isShared_5711_; uint8_t v_isSharedCheck_5715_; 
v_a_5708_ = lean_ctor_get(v___x_5706_, 0);
v_isSharedCheck_5715_ = !lean_is_exclusive(v___x_5706_);
if (v_isSharedCheck_5715_ == 0)
{
v___x_5710_ = v___x_5706_;
v_isShared_5711_ = v_isSharedCheck_5715_;
goto v_resetjp_5709_;
}
else
{
lean_inc(v_a_5708_);
lean_dec(v___x_5706_);
v___x_5710_ = lean_box(0);
v_isShared_5711_ = v_isSharedCheck_5715_;
goto v_resetjp_5709_;
}
v_resetjp_5709_:
{
lean_object* v___x_5713_; 
if (v_isShared_5711_ == 0)
{
v___x_5713_ = v___x_5710_;
goto v_reusejp_5712_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v_a_5708_);
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
}
}
}
else
{
lean_object* v_val_5716_; lean_object* v___x_5718_; 
v_val_5716_ = lean_ctor_get(v_fst_5661_, 0);
lean_inc(v_val_5716_);
lean_dec_ref_known(v_fst_5661_, 1);
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 0, v_val_5716_);
v___x_5718_ = v___x_5659_;
goto v_reusejp_5717_;
}
else
{
lean_object* v_reuseFailAlloc_5719_; 
v_reuseFailAlloc_5719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5719_, 0, v_val_5716_);
v___x_5718_ = v_reuseFailAlloc_5719_;
goto v_reusejp_5717_;
}
v_reusejp_5717_:
{
return v___x_5718_;
}
}
}
}
else
{
lean_object* v_a_5721_; lean_object* v___x_5723_; uint8_t v_isShared_5724_; uint8_t v_isSharedCheck_5728_; 
v_a_5721_ = lean_ctor_get(v___x_5656_, 0);
v_isSharedCheck_5728_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5728_ == 0)
{
v___x_5723_ = v___x_5656_;
v_isShared_5724_ = v_isSharedCheck_5728_;
goto v_resetjp_5722_;
}
else
{
lean_inc(v_a_5721_);
lean_dec(v___x_5656_);
v___x_5723_ = lean_box(0);
v_isShared_5724_ = v_isSharedCheck_5728_;
goto v_resetjp_5722_;
}
v_resetjp_5722_:
{
lean_object* v___x_5726_; 
if (v_isShared_5724_ == 0)
{
v___x_5726_ = v___x_5723_;
goto v_reusejp_5725_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v_a_5721_);
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
}
}
else
{
lean_object* v_a_5731_; lean_object* v___x_5733_; uint8_t v_isShared_5734_; uint8_t v_isSharedCheck_5738_; 
v_a_5731_ = lean_ctor_get(v___x_5640_, 0);
v_isSharedCheck_5738_ = !lean_is_exclusive(v___x_5640_);
if (v_isSharedCheck_5738_ == 0)
{
v___x_5733_ = v___x_5640_;
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
else
{
lean_inc(v_a_5731_);
lean_dec(v___x_5640_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go___boxed(lean_object* v_passes_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_, lean_object* v_a_5747_, lean_object* v_a_5748_){
_start:
{
lean_object* v_res_5749_; 
v_res_5749_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_5739_, v_a_5740_, v_a_5741_, v_a_5742_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_);
lean_dec(v_a_5747_);
lean_dec_ref(v_a_5746_);
lean_dec(v_a_5745_);
lean_dec_ref(v_a_5744_);
lean_dec(v_a_5743_);
lean_dec_ref(v_a_5742_);
lean_dec(v_a_5741_);
lean_dec_ref(v_a_5740_);
lean_dec(v_passes_5739_);
return v_res_5749_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(lean_object* v_cls_5750_, lean_object* v_msg_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_){
_start:
{
lean_object* v___x_5761_; 
v___x_5761_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___redArg(v_cls_5750_, v_msg_5751_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_);
return v___x_5761_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0___boxed(lean_object* v_cls_5762_, lean_object* v_msg_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_){
_start:
{
lean_object* v_res_5773_; 
v_res_5773_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__0(v_cls_5762_, v_msg_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_);
lean_dec(v___y_5771_);
lean_dec_ref(v___y_5770_);
lean_dec(v___y_5769_);
lean_dec_ref(v___y_5768_);
lean_dec(v___y_5767_);
lean_dec_ref(v___y_5766_);
lean_dec(v___y_5765_);
lean_dec_ref(v___y_5764_);
return v_res_5773_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(lean_object* v_00_u03b1_5774_, lean_object* v_x_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_){
_start:
{
lean_object* v___x_5785_; 
v___x_5785_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___redArg(v_x_5775_);
return v___x_5785_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4___boxed(lean_object* v_00_u03b1_5786_, lean_object* v_x_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_){
_start:
{
lean_object* v_res_5797_; 
v_res_5797_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__4(v_00_u03b1_5786_, v_x_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_, v___y_5794_, v___y_5795_);
lean_dec(v___y_5795_);
lean_dec_ref(v___y_5794_);
lean_dec(v___y_5793_);
lean_dec_ref(v___y_5792_);
lean_dec(v___y_5791_);
lean_dec_ref(v___y_5790_);
lean_dec(v___y_5789_);
lean_dec_ref(v___y_5788_);
return v_res_5797_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(lean_object* v_as_5798_, lean_object* v_as_x27_5799_, lean_object* v_b_5800_, lean_object* v_a_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_){
_start:
{
lean_object* v___x_5811_; 
v___x_5811_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___redArg(v_as_x27_5799_, v_b_5800_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_);
return v___x_5811_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4___boxed(lean_object* v_as_5812_, lean_object* v_as_x27_5813_, lean_object* v_b_5814_, lean_object* v_a_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_){
_start:
{
lean_object* v_res_5825_; 
v_res_5825_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__4(v_as_5812_, v_as_x27_5813_, v_b_5814_, v_a_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_);
lean_dec(v___y_5823_);
lean_dec_ref(v___y_5822_);
lean_dec(v___y_5821_);
lean_dec_ref(v___y_5820_);
lean_dec(v___y_5819_);
lean_dec_ref(v___y_5818_);
lean_dec(v___y_5817_);
lean_dec_ref(v___y_5816_);
lean_dec(v_as_x27_5813_);
lean_dec(v_as_5812_);
return v_res_5825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(lean_object* v_oldTraces_5826_, lean_object* v_data_5827_, lean_object* v_ref_5828_, lean_object* v_msg_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_){
_start:
{
lean_object* v___x_5839_; 
v___x_5839_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___redArg(v_oldTraces_5826_, v_data_5827_, v_ref_5828_, v_msg_5829_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_);
return v___x_5839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3___boxed(lean_object* v_oldTraces_5840_, lean_object* v_data_5841_, lean_object* v_ref_5842_, lean_object* v_msg_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_){
_start:
{
lean_object* v_res_5853_; 
v_res_5853_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go_spec__3_spec__3(v_oldTraces_5840_, v_data_5841_, v_ref_5842_, v_msg_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_);
lean_dec(v___y_5851_);
lean_dec_ref(v___y_5850_);
lean_dec(v___y_5849_);
lean_dec_ref(v___y_5848_);
lean_dec(v___y_5847_);
lean_dec_ref(v___y_5846_);
lean_dec(v___y_5845_);
lean_dec_ref(v___y_5844_);
return v_res_5853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(lean_object* v_passes_5854_, lean_object* v_a_5855_, lean_object* v_a_5856_, lean_object* v_a_5857_, lean_object* v_a_5858_, lean_object* v_a_5859_, lean_object* v_a_5860_, lean_object* v_a_5861_, lean_object* v_a_5862_){
_start:
{
lean_object* v___x_5864_; 
v___x_5864_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Basic_0__Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_go(v_passes_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_, v_a_5859_, v_a_5860_, v_a_5861_, v_a_5862_);
if (lean_obj_tag(v___x_5864_) == 0)
{
lean_object* v_a_5865_; lean_object* v___x_5866_; lean_object* v___x_5868_; uint8_t v_isShared_5869_; uint8_t v_isSharedCheck_5873_; 
v_a_5865_ = lean_ctor_get(v___x_5864_, 0);
lean_inc(v_a_5865_);
lean_dec_ref_known(v___x_5864_, 1);
v___x_5866_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dropFixpointCaches___redArg(v_a_5856_);
v_isSharedCheck_5873_ = !lean_is_exclusive(v___x_5866_);
if (v_isSharedCheck_5873_ == 0)
{
lean_object* v_unused_5874_; 
v_unused_5874_ = lean_ctor_get(v___x_5866_, 0);
lean_dec(v_unused_5874_);
v___x_5868_ = v___x_5866_;
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
else
{
lean_dec(v___x_5866_);
v___x_5868_ = lean_box(0);
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
v_resetjp_5867_:
{
lean_object* v___x_5871_; 
if (v_isShared_5869_ == 0)
{
lean_ctor_set(v___x_5868_, 0, v_a_5865_);
v___x_5871_ = v___x_5868_;
goto v_reusejp_5870_;
}
else
{
lean_object* v_reuseFailAlloc_5872_; 
v_reuseFailAlloc_5872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5872_, 0, v_a_5865_);
v___x_5871_ = v_reuseFailAlloc_5872_;
goto v_reusejp_5870_;
}
v_reusejp_5870_:
{
return v___x_5871_;
}
}
}
else
{
return v___x_5864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(lean_object* v_passes_5875_, lean_object* v_a_5876_, lean_object* v_a_5877_, lean_object* v_a_5878_, lean_object* v_a_5879_, lean_object* v_a_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_){
_start:
{
lean_object* v_res_5885_; 
v_res_5885_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(v_passes_5875_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_);
lean_dec(v_a_5883_);
lean_dec_ref(v_a_5882_);
lean_dec(v_a_5881_);
lean_dec_ref(v_a_5880_);
lean_dec(v_a_5879_);
lean_dec_ref(v_a_5878_);
lean_dec(v_a_5877_);
lean_dec_ref(v_a_5876_);
lean_dec(v_passes_5875_);
return v_res_5885_;
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
