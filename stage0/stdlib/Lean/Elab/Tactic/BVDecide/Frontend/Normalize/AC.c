// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.AC
// Imports: public import Lean.Meta.Tactic.AC.Main public import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_merge___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_checkEmoji;
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMul"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 82, 7, 193, 128, 145, 145, 228)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Op.mul"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "internal error (this is a bug!): index "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = " out of range, the current state only has "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " variables:\n\n"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Found binary operation '"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "', expected '"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "'.Treating as atom."};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "canonicalizeWithSharing"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Operations mismatch:\n      the left-hand-side has operation "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n        "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\n      but the right-hand-side has operation "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8;
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Canonicalizing with respect to operation: '"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to recognize operation: "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Canonicalizing: "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__2_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__3_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_ac_nf "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " found `BEq.beq`."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " found `Eq`."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0___boxed__const__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0___boxed__const__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0___boxed, .m_arity = 9, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0___boxed__const__1_value)} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0_value;
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_ac_nf"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 2, 240, 42, 244, 93, 182, 215)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___closed__3_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType(lean_object* v_w_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__2);
v___x_9_ = l_Lean_Expr_app___override(v___x_8_, v_w_7_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_box(0);
v___x_15_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__1));
v___x_16_ = l_Lean_Expr_const___override(v___x_15_, v___x_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul(lean_object* v_w_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul___closed__2);
v___x_19_ = l_Lean_Expr_app___override(v___x_18_, v_w_17_);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__2));
v___x_27_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__1));
v___x_28_ = l_Lean_mkConst(v___x_27_, v___x_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul(lean_object* v_w_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_30_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul___closed__3);
lean_inc_ref(v_w_29_);
v___x_31_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType(v_w_29_);
v___x_32_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstMul(v_w_29_);
v___x_33_ = l_Lean_mkAppB(v___x_30_, v___x_31_, v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__2(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_box(0);
v___x_39_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__1));
v___x_40_ = l_Lean_mkConst(v___x_39_, v___x_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit(lean_object* v_w_41_, lean_object* v_n_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit___closed__2);
v___x_44_ = l_Lean_mkNatLit(v_n_42_);
v___x_45_ = l_Lean_mkAppB(v___x_43_, v_w_41_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp_beq(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = lean_expr_eqv(v_x_46_, v_x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp_beq___boxed(lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instBEqOp_beq(v_x_49_, v_x_50_);
lean_dec_ref(v_x_50_);
lean_dec_ref(v_x_49_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__3(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(2u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__4(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_to_int(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr(lean_object* v_x_65_, lean_object* v_prec_66_){
_start:
{
lean_object* v___y_68_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1024u);
v___x_78_ = lean_nat_dec_le(v___x_77_, v_prec_66_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__3);
v___y_68_ = v___x_79_;
goto v___jp_67_;
}
else
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__4);
v___y_68_ = v___x_80_;
goto v___jp_67_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_69_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___closed__2));
v___x_70_ = lean_unsigned_to_nat(1024u);
v___x_71_ = l_Lean_instReprExpr_repr(v_x_65_, v___x_70_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_69_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
lean_inc(v___y_68_);
v___x_73_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_73_, 0, v___y_68_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = 0;
v___x_75_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_74_);
v___x_76_ = l_Repr_addAppParen(v___x_75_, v_prec_66_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr___boxed(lean_object* v_x_81_, lean_object* v_prec_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_instReprOp_repr(v_x_81_, v_prec_82_);
lean_dec(v_prec_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f(lean_object* v_e_91_){
_start:
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = l_Lean_Expr_cleanupAnnotations(v_e_91_);
v___x_93_ = l_Lean_Expr_isApp(v___x_92_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec_ref(v___x_92_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = l_Lean_Expr_appFnCleanup___redArg(v___x_92_);
v___x_96_ = l_Lean_Expr_isApp(v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec_ref(v___x_95_);
v___x_97_ = lean_box(0);
return v___x_97_;
}
else
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = l_Lean_Expr_appFnCleanup___redArg(v___x_95_);
v___x_99_ = l_Lean_Expr_isApp(v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec_ref(v___x_98_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = l_Lean_Expr_appFnCleanup___redArg(v___x_98_);
v___x_102_ = l_Lean_Expr_isApp(v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_dec_ref(v___x_101_);
v___x_103_ = lean_box(0);
return v___x_103_;
}
else
{
lean_object* v_arg_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v_arg_104_ = lean_ctor_get(v___x_101_, 1);
lean_inc_ref(v_arg_104_);
v___x_105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_101_);
v___x_106_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2));
v___x_107_ = l_Lean_Expr_isConstOf(v___x_105_, v___x_106_);
lean_dec_ref(v___x_105_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
lean_dec_ref(v_arg_104_);
v___x_108_ = lean_box(0);
return v___x_108_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = l_Lean_Expr_cleanupAnnotations(v_arg_104_);
v___x_110_ = l_Lean_Expr_isApp(v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
lean_dec_ref(v___x_109_);
v___x_111_ = lean_box(0);
return v___x_111_;
}
else
{
lean_object* v_arg_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_arg_112_ = lean_ctor_get(v___x_109_, 1);
lean_inc_ref(v_arg_112_);
v___x_113_ = l_Lean_Expr_appFnCleanup___redArg(v___x_109_);
v___x_114_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType___closed__1));
v___x_115_ = l_Lean_Expr_isConstOf(v___x_113_, v___x_114_);
lean_dec_ref(v___x_113_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
lean_dec_ref(v_arg_112_);
v___x_116_ = lean_box(0);
return v___x_116_;
}
else
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v_arg_112_);
return v___x_117_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(lean_object* v_x_118_){
_start:
{
if (lean_obj_tag(v_x_118_) == 5)
{
lean_object* v_fn_119_; 
v_fn_119_ = lean_ctor_get(v_x_118_, 0);
lean_inc_ref(v_fn_119_);
lean_dec_ref(v_x_118_);
if (lean_obj_tag(v_fn_119_) == 5)
{
lean_object* v_fn_120_; lean_object* v___x_121_; 
v_fn_120_ = lean_ctor_get(v_fn_119_, 0);
lean_inc_ref(v_fn_120_);
lean_dec_ref(v_fn_119_);
v___x_121_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f(v_fn_120_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; 
lean_dec_ref(v_fn_119_);
v___x_122_ = lean_box(0);
return v___x_122_;
}
}
else
{
lean_object* v___x_123_; 
lean_dec_ref(v_x_118_);
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = l_Lean_Level_ofNat(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
v___x_127_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0);
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__2(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__1);
v___x_130_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__3(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__2);
v___x_133_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__0);
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__4(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__3);
v___x_136_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f___closed__2));
v___x_137_ = l_Lean_mkConst(v___x_136_, v___x_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(lean_object* v_x_138_){
_start:
{
lean_object* v_bv_139_; lean_object* v_inst_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
lean_inc_ref(v_x_138_);
v_bv_139_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkType(v_x_138_);
v_inst_140_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_BitVec_mkInstHMul(v_x_138_);
v___x_141_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr___closed__4);
lean_inc_ref_n(v_bv_139_, 2);
v___x_142_ = l_Lean_mkApp4(v___x_141_, v_bv_139_, v_bv_139_, v_bv_139_, v_inst_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(lean_object* v_x_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_mkBitVecLit(v_x_143_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg(lean_object* v_op_x27_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofExpr_x3f(v_op_x27_146_);
if (lean_obj_tag(v___x_147_) == 1)
{
uint8_t v___x_148_; 
lean_dec_ref(v___x_147_);
v___x_148_ = 1;
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
lean_dec(v___x_147_);
v___x_149_ = 0;
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg___boxed(lean_object* v_op_x27_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg(v_op_x27_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind(lean_object* v_op_153_, lean_object* v_op_x27_154_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg(v_op_x27_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___boxed(lean_object* v_op_156_, lean_object* v_op_x27_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind(v_op_156_, v_op_x27_157_);
lean_dec_ref(v_op_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_instToMessageData___lam__0(lean_object* v_op_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_op_160_);
v___x_162_ = l_Lean_MessageData_ofExpr(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(lean_object* v_x_165_, lean_object* v_s_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___x_172_; 
lean_inc(v_a_170_);
lean_inc_ref(v_a_169_);
lean_inc(v_a_168_);
lean_inc_ref(v_a_167_);
v___x_172_ = lean_apply_6(v_x_165_, v_s_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, lean_box(0));
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_181_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v_fst_177_; lean_object* v___x_179_; 
v_fst_177_ = lean_ctor_get(v_a_173_, 0);
lean_inc(v_fst_177_);
lean_dec(v_a_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v_fst_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_fst_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
v_a_182_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_172_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_172_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg___boxed(lean_object* v_x_190_, lean_object* v_s_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v_x_190_, v_s_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27(lean_object* v_00_u03b1_198_, lean_object* v_x_199_, lean_object* v_s_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v_x_199_, v_s_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___boxed(lean_object* v_00_u03b1_207_, lean_object* v_x_208_, lean_object* v_s_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27(v_00_u03b1_207_, v_x_208_, v_s_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object* v_a_216_, lean_object* v_x_217_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(0);
return v___x_218_;
}
else
{
lean_object* v_key_219_; lean_object* v_value_220_; lean_object* v_tail_221_; uint8_t v___x_222_; 
v_key_219_ = lean_ctor_get(v_x_217_, 0);
v_value_220_ = lean_ctor_get(v_x_217_, 1);
v_tail_221_ = lean_ctor_get(v_x_217_, 2);
v___x_222_ = lean_expr_eqv(v_key_219_, v_a_216_);
if (v___x_222_ == 0)
{
v_x_217_ = v_tail_221_;
goto _start;
}
else
{
lean_object* v___x_224_; 
lean_inc(v_value_220_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v_value_220_);
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_225_, lean_object* v_x_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_225_, v_x_226_);
lean_dec(v_x_226_);
lean_dec_ref(v_a_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object* v_m_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_buckets_230_; lean_object* v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v_fold_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_buckets_230_ = lean_ctor_get(v_m_228_, 1);
v___x_231_ = lean_array_get_size(v_buckets_230_);
v___x_232_ = l_Lean_Expr_hash(v_a_229_);
v___x_233_ = 32ULL;
v___x_234_ = lean_uint64_shift_right(v___x_232_, v___x_233_);
v_fold_235_ = lean_uint64_xor(v___x_232_, v___x_234_);
v___x_236_ = 16ULL;
v___x_237_ = lean_uint64_shift_right(v_fold_235_, v___x_236_);
v___x_238_ = lean_uint64_xor(v_fold_235_, v___x_237_);
v___x_239_ = lean_uint64_to_usize(v___x_238_);
v___x_240_ = lean_usize_of_nat(v___x_231_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_sub(v___x_240_, v___x_241_);
v___x_243_ = lean_usize_land(v___x_239_, v___x_242_);
v___x_244_ = lean_array_uget_borrowed(v_buckets_230_, v___x_243_);
v___x_245_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_229_, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object* v_m_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_246_, v_a_247_);
lean_dec_ref(v_a_247_);
lean_dec_ref(v_m_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
return v_x_249_;
}
else
{
lean_object* v_key_251_; lean_object* v_value_252_; lean_object* v_tail_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_276_; 
v_key_251_ = lean_ctor_get(v_x_250_, 0);
v_value_252_ = lean_ctor_get(v_x_250_, 1);
v_tail_253_ = lean_ctor_get(v_x_250_, 2);
v_isSharedCheck_276_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_276_ == 0)
{
v___x_255_ = v_x_250_;
v_isShared_256_ = v_isSharedCheck_276_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_tail_253_);
lean_inc(v_value_252_);
lean_inc(v_key_251_);
lean_dec(v_x_250_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_276_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; uint64_t v___x_258_; uint64_t v___x_259_; uint64_t v___x_260_; uint64_t v_fold_261_; uint64_t v___x_262_; uint64_t v___x_263_; uint64_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; size_t v___x_268_; size_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_257_ = lean_array_get_size(v_x_249_);
v___x_258_ = l_Lean_Expr_hash(v_key_251_);
v___x_259_ = 32ULL;
v___x_260_ = lean_uint64_shift_right(v___x_258_, v___x_259_);
v_fold_261_ = lean_uint64_xor(v___x_258_, v___x_260_);
v___x_262_ = 16ULL;
v___x_263_ = lean_uint64_shift_right(v_fold_261_, v___x_262_);
v___x_264_ = lean_uint64_xor(v_fold_261_, v___x_263_);
v___x_265_ = lean_uint64_to_usize(v___x_264_);
v___x_266_ = lean_usize_of_nat(v___x_257_);
v___x_267_ = ((size_t)1ULL);
v___x_268_ = lean_usize_sub(v___x_266_, v___x_267_);
v___x_269_ = lean_usize_land(v___x_265_, v___x_268_);
v___x_270_ = lean_array_uget_borrowed(v_x_249_, v___x_269_);
lean_inc(v___x_270_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 2, v___x_270_);
v___x_272_ = v___x_255_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_key_251_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_value_252_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v___x_270_);
v___x_272_ = v_reuseFailAlloc_275_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; 
v___x_273_ = lean_array_uset(v_x_249_, v___x_269_, v___x_272_);
v_x_249_ = v___x_273_;
v_x_250_ = v_tail_253_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(lean_object* v_i_277_, lean_object* v_source_278_, lean_object* v_target_279_){
_start:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_array_get_size(v_source_278_);
v___x_281_ = lean_nat_dec_lt(v_i_277_, v___x_280_);
if (v___x_281_ == 0)
{
lean_dec_ref(v_source_278_);
lean_dec(v_i_277_);
return v_target_279_;
}
else
{
lean_object* v_es_282_; lean_object* v___x_283_; lean_object* v_source_284_; lean_object* v_target_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_es_282_ = lean_array_fget(v_source_278_, v_i_277_);
v___x_283_ = lean_box(0);
v_source_284_ = lean_array_fset(v_source_278_, v_i_277_, v___x_283_);
v_target_285_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_279_, v_es_282_);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_i_277_, v___x_286_);
lean_dec(v_i_277_);
v_i_277_ = v___x_287_;
v_source_278_ = v_source_284_;
v_target_279_ = v_target_285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(lean_object* v_data_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_nbuckets_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_290_ = lean_array_get_size(v_data_289_);
v___x_291_ = lean_unsigned_to_nat(2u);
v_nbuckets_292_ = lean_nat_mul(v___x_290_, v___x_291_);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_box(0);
v___x_295_ = lean_mk_array(v_nbuckets_292_, v___x_294_);
v___x_296_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v___x_293_, v_data_289_, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(lean_object* v_a_297_, lean_object* v_b_298_, lean_object* v_x_299_){
_start:
{
if (lean_obj_tag(v_x_299_) == 0)
{
lean_dec(v_b_298_);
lean_dec_ref(v_a_297_);
return v_x_299_;
}
else
{
lean_object* v_key_300_; lean_object* v_value_301_; lean_object* v_tail_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_314_; 
v_key_300_ = lean_ctor_get(v_x_299_, 0);
v_value_301_ = lean_ctor_get(v_x_299_, 1);
v_tail_302_ = lean_ctor_get(v_x_299_, 2);
v_isSharedCheck_314_ = !lean_is_exclusive(v_x_299_);
if (v_isSharedCheck_314_ == 0)
{
v___x_304_ = v_x_299_;
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_tail_302_);
lean_inc(v_value_301_);
lean_inc(v_key_300_);
lean_dec(v_x_299_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_314_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
uint8_t v___x_306_; 
v___x_306_ = lean_expr_eqv(v_key_300_, v_a_297_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_307_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_297_, v_b_298_, v_tail_302_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 2, v___x_307_);
v___x_309_ = v___x_304_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_key_300_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_value_301_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
else
{
lean_object* v___x_312_; 
lean_dec(v_value_301_);
lean_dec(v_key_300_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 1, v_b_298_);
lean_ctor_set(v___x_304_, 0, v_a_297_);
v___x_312_ = v___x_304_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_297_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_b_298_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_tail_302_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object* v_a_315_, lean_object* v_x_316_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
uint8_t v___x_317_; 
v___x_317_ = 0;
return v___x_317_;
}
else
{
lean_object* v_key_318_; lean_object* v_tail_319_; uint8_t v___x_320_; 
v_key_318_ = lean_ctor_get(v_x_316_, 0);
v_tail_319_ = lean_ctor_get(v_x_316_, 2);
v___x_320_ = lean_expr_eqv(v_key_318_, v_a_315_);
if (v___x_320_ == 0)
{
v_x_316_ = v_tail_319_;
goto _start;
}
else
{
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object* v_a_322_, lean_object* v_x_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_322_, v_x_323_);
lean_dec(v_x_323_);
lean_dec_ref(v_a_322_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object* v_m_326_, lean_object* v_a_327_, lean_object* v_b_328_){
_start:
{
lean_object* v_size_329_; lean_object* v_buckets_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_373_; 
v_size_329_ = lean_ctor_get(v_m_326_, 0);
v_buckets_330_ = lean_ctor_get(v_m_326_, 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v_m_326_);
if (v_isSharedCheck_373_ == 0)
{
v___x_332_ = v_m_326_;
v_isShared_333_ = v_isSharedCheck_373_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_buckets_330_);
lean_inc(v_size_329_);
lean_dec(v_m_326_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_373_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v_fold_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; lean_object* v_bkt_347_; uint8_t v___x_348_; 
v___x_334_ = lean_array_get_size(v_buckets_330_);
v___x_335_ = l_Lean_Expr_hash(v_a_327_);
v___x_336_ = 32ULL;
v___x_337_ = lean_uint64_shift_right(v___x_335_, v___x_336_);
v_fold_338_ = lean_uint64_xor(v___x_335_, v___x_337_);
v___x_339_ = 16ULL;
v___x_340_ = lean_uint64_shift_right(v_fold_338_, v___x_339_);
v___x_341_ = lean_uint64_xor(v_fold_338_, v___x_340_);
v___x_342_ = lean_uint64_to_usize(v___x_341_);
v___x_343_ = lean_usize_of_nat(v___x_334_);
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_sub(v___x_343_, v___x_344_);
v___x_346_ = lean_usize_land(v___x_342_, v___x_345_);
v_bkt_347_ = lean_array_uget_borrowed(v_buckets_330_, v___x_346_);
v___x_348_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_327_, v_bkt_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v_size_x27_350_; lean_object* v___x_351_; lean_object* v_buckets_x27_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_349_ = lean_unsigned_to_nat(1u);
v_size_x27_350_ = lean_nat_add(v_size_329_, v___x_349_);
lean_dec(v_size_329_);
lean_inc(v_bkt_347_);
v___x_351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_351_, 0, v_a_327_);
lean_ctor_set(v___x_351_, 1, v_b_328_);
lean_ctor_set(v___x_351_, 2, v_bkt_347_);
v_buckets_x27_352_ = lean_array_uset(v_buckets_330_, v___x_346_, v___x_351_);
v___x_353_ = lean_unsigned_to_nat(4u);
v___x_354_ = lean_nat_mul(v_size_x27_350_, v___x_353_);
v___x_355_ = lean_unsigned_to_nat(3u);
v___x_356_ = lean_nat_div(v___x_354_, v___x_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_array_get_size(v_buckets_x27_352_);
v___x_358_ = lean_nat_dec_le(v___x_356_, v___x_357_);
lean_dec(v___x_356_);
if (v___x_358_ == 0)
{
lean_object* v_val_359_; lean_object* v___x_361_; 
v_val_359_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_buckets_x27_352_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_val_359_);
lean_ctor_set(v___x_332_, 0, v_size_x27_350_);
v___x_361_ = v___x_332_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_size_x27_350_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_val_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
else
{
lean_object* v___x_364_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_buckets_x27_352_);
lean_ctor_set(v___x_332_, 0, v_size_x27_350_);
v___x_364_ = v___x_332_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_size_x27_350_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_buckets_x27_352_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_object* v___x_366_; lean_object* v_buckets_x27_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
lean_inc(v_bkt_347_);
v___x_366_ = lean_box(0);
v_buckets_x27_367_ = lean_array_uset(v_buckets_330_, v___x_346_, v___x_366_);
v___x_368_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_327_, v_b_328_, v_bkt_347_);
v___x_369_ = lean_array_uset(v_buckets_x27_367_, v___x_346_, v___x_368_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_369_);
v___x_371_ = v___x_332_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_size_329_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg(lean_object* v_e_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_op_377_; lean_object* v_exprToVarIndex_378_; lean_object* v_varToExpr_379_; lean_object* v___x_380_; 
v_op_377_ = lean_ctor_get(v_a_375_, 0);
v_exprToVarIndex_378_ = lean_ctor_get(v_a_375_, 1);
v_varToExpr_379_ = lean_ctor_get(v_a_375_, 2);
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg(v_exprToVarIndex_378_, v_e_374_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_392_; 
lean_inc_ref(v_varToExpr_379_);
lean_inc_ref(v_exprToVarIndex_378_);
lean_inc_ref(v_op_377_);
v_isSharedCheck_392_ = !lean_is_exclusive(v_a_375_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; lean_object* v_unused_394_; lean_object* v_unused_395_; 
v_unused_393_ = lean_ctor_get(v_a_375_, 2);
lean_dec(v_unused_393_);
v_unused_394_ = lean_ctor_get(v_a_375_, 1);
lean_dec(v_unused_394_);
v_unused_395_ = lean_ctor_get(v_a_375_, 0);
lean_dec(v_unused_395_);
v___x_382_ = v_a_375_;
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
else
{
lean_dec(v_a_375_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_392_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_size_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v_size_384_ = lean_ctor_get(v_exprToVarIndex_378_, 0);
lean_inc_n(v_size_384_, 2);
lean_inc_ref(v_e_374_);
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1___redArg(v_exprToVarIndex_378_, v_e_374_, v_size_384_);
v___x_386_ = lean_array_push(v_varToExpr_379_, v_e_374_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 2, v___x_386_);
lean_ctor_set(v___x_382_, 1, v___x_385_);
v___x_388_ = v___x_382_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_op_377_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v___x_386_);
v___x_388_ = v_reuseFailAlloc_391_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_size_384_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
}
else
{
lean_object* v_val_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
lean_dec_ref(v_e_374_);
v_val_396_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v___x_380_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_val_396_);
lean_dec(v___x_380_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_val_396_);
lean_ctor_set(v___x_400_, 1, v_a_375_);
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 0);
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object* v_e_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg(v_e_405_, v_a_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar(lean_object* v_e_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg(v_e_409_, v_a_410_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___boxed(lean_object* v_e_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar(v_e_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0(lean_object* v_00_u03b2_425_, lean_object* v_m_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_426_, v_a_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object* v_00_u03b2_429_, lean_object* v_m_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0(v_00_u03b2_429_, v_m_430_, v_a_431_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v_m_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1(lean_object* v_00_u03b2_433_, lean_object* v_m_434_, lean_object* v_a_435_, lean_object* v_b_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1___redArg(v_m_434_, v_a_435_, v_b_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object* v_00_u03b2_438_, lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_439_, v_x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_442_, lean_object* v_a_443_, lean_object* v_x_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__0_spec__0(v_00_u03b2_442_, v_a_443_, v_x_444_);
lean_dec(v_x_444_);
lean_dec_ref(v_a_443_);
return v_res_445_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object* v_00_u03b2_446_, lean_object* v_a_447_, lean_object* v_x_448_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_447_, v_x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_450_, lean_object* v_a_451_, lean_object* v_x_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__2(v_00_u03b2_450_, v_a_451_, v_x_452_);
lean_dec(v_x_452_);
lean_dec_ref(v_a_451_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3(lean_object* v_00_u03b2_455_, lean_object* v_data_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_data_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4(lean_object* v_00_u03b2_458_, lean_object* v_a_459_, lean_object* v_b_460_, lean_object* v_x_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_459_, v_b_460_, v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_463_, lean_object* v_i_464_, lean_object* v_source_465_, lean_object* v_target_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v_i_464_, v_source_465_, v_target_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object* v_msgData_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; lean_object* v_env_479_; lean_object* v___x_480_; lean_object* v_mctx_481_; lean_object* v_lctx_482_; lean_object* v_options_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_478_ = lean_st_ref_get(v___y_476_);
v_env_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc_ref(v_env_479_);
lean_dec(v___x_478_);
v___x_480_ = lean_st_ref_get(v___y_474_);
v_mctx_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_ref(v_mctx_481_);
lean_dec(v___x_480_);
v_lctx_482_ = lean_ctor_get(v___y_473_, 2);
v_options_483_ = lean_ctor_get(v___y_475_, 2);
lean_inc_ref(v_options_483_);
lean_inc_ref(v_lctx_482_);
v___x_484_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_484_, 0, v_env_479_);
lean_ctor_set(v___x_484_, 1, v_mctx_481_);
lean_ctor_set(v___x_484_, 2, v_lctx_482_);
lean_ctor_set(v___x_484_, 3, v_options_483_);
v___x_485_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_msgData_472_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object* v_msgData_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msgData_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object* v_msg_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_ref_500_; lean_object* v___x_501_; lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_510_; 
v_ref_500_ = lean_ctor_get(v___y_497_, 5);
v___x_501_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_510_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_508_; 
lean_inc(v_ref_500_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_ref_500_);
lean_ctor_set(v___x_506_, 1, v_a_502_);
if (v_isShared_505_ == 0)
{
lean_ctor_set_tag(v___x_504_, 1);
lean_ctor_set(v___x_504_, 0, v___x_506_);
v___x_508_ = v___x_504_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object* v_msg_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__0(lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
if (lean_obj_tag(v_a_518_) == 0)
{
lean_object* v___x_520_; 
v___x_520_ = l_List_reverse___redArg(v_a_519_);
return v___x_520_;
}
else
{
lean_object* v_head_521_; lean_object* v_tail_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_531_; 
v_head_521_ = lean_ctor_get(v_a_518_, 0);
v_tail_522_ = lean_ctor_get(v_a_518_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_a_518_);
if (v_isSharedCheck_531_ == 0)
{
v___x_524_ = v_a_518_;
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_tail_522_);
lean_inc(v_head_521_);
lean_dec(v_a_518_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_526_ = l_Lean_MessageData_ofExpr(v_head_521_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 1, v_a_519_);
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_a_519_);
v___x_528_ = v_reuseFailAlloc_530_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v_a_518_ = v_tail_522_;
v_a_519_ = v___x_528_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__1(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__0));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__3(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__2));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__5(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__4));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr(lean_object* v_idx_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_varToExpr_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_varToExpr_548_ = lean_ctor_get(v_a_542_, 2);
v___x_549_ = lean_array_get_size(v_varToExpr_548_);
v___x_550_ = lean_nat_dec_lt(v_idx_541_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_inc_ref(v_varToExpr_548_);
lean_dec_ref(v_a_542_);
v___x_551_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__1);
v___x_552_ = l_Nat_reprFast(v_idx_541_);
v___x_553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
v___x_554_ = l_Lean_MessageData_ofFormat(v___x_553_);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_551_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__3);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = l_Nat_reprFast(v___x_549_);
v___x_559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___x_560_ = l_Lean_MessageData_ofFormat(v___x_559_);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_557_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___closed__5);
v___x_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_array_to_list(v_varToExpr_548_);
v___x_565_ = lean_box(0);
v___x_566_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__0(v___x_564_, v___x_565_);
v___x_567_ = l_Lean_MessageData_ofList(v___x_566_);
v___x_568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_563_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg(v___x_568_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
return v___x_569_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_array_fget(v_varToExpr_548_, v_idx_541_);
lean_dec(v_idx_541_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_a_542_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr___boxed(lean_object* v_idx_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr(v_idx_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1(lean_object* v_00_u03b1_581_, lean_object* v_msg_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_582_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object* v_00_u03b1_590_, lean_object* v_msg_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1(v_00_u03b1_590_, v_msg_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec_ref(v___y_592_);
return v_res_598_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object* v_a_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
uint8_t v___x_601_; 
v___x_601_ = 0;
return v___x_601_;
}
else
{
lean_object* v_key_602_; lean_object* v_tail_603_; uint8_t v___x_604_; 
v_key_602_ = lean_ctor_get(v_x_600_, 0);
v_tail_603_ = lean_ctor_get(v_x_600_, 2);
v___x_604_ = lean_nat_dec_eq(v_key_602_, v_a_599_);
if (v___x_604_ == 0)
{
v_x_600_ = v_tail_603_;
goto _start;
}
else
{
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_606_, lean_object* v_x_607_){
_start:
{
uint8_t v_res_608_; lean_object* v_r_609_; 
v_res_608_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_606_, v_x_607_);
lean_dec(v_x_607_);
lean_dec(v_a_606_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object* v_c_610_){
_start:
{
lean_object* v___y_612_; 
if (lean_obj_tag(v_c_610_) == 0)
{
lean_object* v___x_616_; 
v___x_616_ = lean_unsigned_to_nat(0u);
v___y_612_ = v___x_616_;
goto v___jp_611_;
}
else
{
lean_object* v_val_617_; 
v_val_617_ = lean_ctor_get(v_c_610_, 0);
v___y_612_ = v_val_617_;
goto v___jp_611_;
}
v___jp_611_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_add(v___y_612_, v___x_613_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object* v_c_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v_c_618_);
lean_dec(v_c_618_);
return v_res_619_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_box(0);
v___x_621_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object* v_a_622_, lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_623_) == 0)
{
lean_object* v___x_624_; lean_object* v_val_625_; lean_object* v___x_626_; 
v___x_624_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0);
v_val_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_val_625_);
v___x_626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_626_, 0, v_a_622_);
lean_ctor_set(v___x_626_, 1, v_val_625_);
lean_ctor_set(v___x_626_, 2, v_x_623_);
return v___x_626_;
}
else
{
lean_object* v_key_627_; lean_object* v_value_628_; lean_object* v_tail_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_644_; 
v_key_627_ = lean_ctor_get(v_x_623_, 0);
v_value_628_ = lean_ctor_get(v_x_623_, 1);
v_tail_629_ = lean_ctor_get(v_x_623_, 2);
v_isSharedCheck_644_ = !lean_is_exclusive(v_x_623_);
if (v_isSharedCheck_644_ == 0)
{
v___x_631_ = v_x_623_;
v_isShared_632_ = v_isSharedCheck_644_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_tail_629_);
lean_inc(v_value_628_);
lean_inc(v_key_627_);
lean_dec(v_x_623_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_644_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
uint8_t v___x_633_; 
v___x_633_ = lean_nat_dec_eq(v_key_627_, v_a_622_);
if (v___x_633_ == 0)
{
lean_object* v_tail_634_; lean_object* v___x_636_; 
v_tail_634_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_622_, v_tail_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 2, v_tail_634_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_key_627_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_value_628_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_tail_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_val_640_; lean_object* v___x_642_; 
lean_dec(v_key_627_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v_value_628_);
v___x_639_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_638_);
lean_dec_ref(v___x_638_);
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec(v___x_639_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v_val_640_);
lean_ctor_set(v___x_631_, 0, v_a_622_);
v___x_642_ = v___x_631_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_622_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_val_640_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_tail_629_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
if (lean_obj_tag(v_x_646_) == 0)
{
return v_x_645_;
}
else
{
lean_object* v_key_647_; lean_object* v_value_648_; lean_object* v_tail_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_672_; 
v_key_647_ = lean_ctor_get(v_x_646_, 0);
v_value_648_ = lean_ctor_get(v_x_646_, 1);
v_tail_649_ = lean_ctor_get(v_x_646_, 2);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_646_);
if (v_isSharedCheck_672_ == 0)
{
v___x_651_ = v_x_646_;
v_isShared_652_ = v_isSharedCheck_672_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_tail_649_);
lean_inc(v_value_648_);
lean_inc(v_key_647_);
lean_dec(v_x_646_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_672_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; uint64_t v___x_654_; uint64_t v___x_655_; uint64_t v___x_656_; uint64_t v_fold_657_; uint64_t v___x_658_; uint64_t v___x_659_; uint64_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_653_ = lean_array_get_size(v_x_645_);
v___x_654_ = lean_uint64_of_nat(v_key_647_);
v___x_655_ = 32ULL;
v___x_656_ = lean_uint64_shift_right(v___x_654_, v___x_655_);
v_fold_657_ = lean_uint64_xor(v___x_654_, v___x_656_);
v___x_658_ = 16ULL;
v___x_659_ = lean_uint64_shift_right(v_fold_657_, v___x_658_);
v___x_660_ = lean_uint64_xor(v_fold_657_, v___x_659_);
v___x_661_ = lean_uint64_to_usize(v___x_660_);
v___x_662_ = lean_usize_of_nat(v___x_653_);
v___x_663_ = ((size_t)1ULL);
v___x_664_ = lean_usize_sub(v___x_662_, v___x_663_);
v___x_665_ = lean_usize_land(v___x_661_, v___x_664_);
v___x_666_ = lean_array_uget_borrowed(v_x_645_, v___x_665_);
lean_inc(v___x_666_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 2, v___x_666_);
v___x_668_ = v___x_651_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_key_647_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_value_648_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v___x_666_);
v___x_668_ = v_reuseFailAlloc_671_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; 
v___x_669_ = lean_array_uset(v_x_645_, v___x_665_, v___x_668_);
v_x_645_ = v___x_669_;
v_x_646_ = v_tail_649_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_673_, lean_object* v_source_674_, lean_object* v_target_675_){
_start:
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = lean_array_get_size(v_source_674_);
v___x_677_ = lean_nat_dec_lt(v_i_673_, v___x_676_);
if (v___x_677_ == 0)
{
lean_dec_ref(v_source_674_);
lean_dec(v_i_673_);
return v_target_675_;
}
else
{
lean_object* v_es_678_; lean_object* v___x_679_; lean_object* v_source_680_; lean_object* v_target_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_es_678_ = lean_array_fget(v_source_674_, v_i_673_);
v___x_679_ = lean_box(0);
v_source_680_ = lean_array_fset(v_source_674_, v_i_673_, v___x_679_);
v_target_681_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_675_, v_es_678_);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_add(v_i_673_, v___x_682_);
lean_dec(v_i_673_);
v_i_673_ = v___x_683_;
v_source_674_ = v_source_680_;
v_target_675_ = v_target_681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object* v_data_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_nbuckets_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_686_ = lean_array_get_size(v_data_685_);
v___x_687_ = lean_unsigned_to_nat(2u);
v_nbuckets_688_ = lean_nat_mul(v___x_686_, v___x_687_);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = lean_box(0);
v___x_691_ = lean_mk_array(v_nbuckets_688_, v___x_690_);
v___x_692_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v___x_689_, v_data_685_, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object* v_m_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_size_695_; lean_object* v_buckets_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_744_; 
v_size_695_ = lean_ctor_get(v_m_693_, 0);
v_buckets_696_ = lean_ctor_get(v_m_693_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_m_693_);
if (v_isSharedCheck_744_ == 0)
{
v___x_698_ = v_m_693_;
v_isShared_699_ = v_isSharedCheck_744_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_buckets_696_);
lean_inc(v_size_695_);
lean_dec(v_m_693_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_744_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v_fold_704_; uint64_t v___x_705_; uint64_t v___x_706_; uint64_t v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; lean_object* v_bkt_713_; uint8_t v___x_714_; 
v___x_700_ = lean_array_get_size(v_buckets_696_);
v___x_701_ = lean_uint64_of_nat(v_a_694_);
v___x_702_ = 32ULL;
v___x_703_ = lean_uint64_shift_right(v___x_701_, v___x_702_);
v_fold_704_ = lean_uint64_xor(v___x_701_, v___x_703_);
v___x_705_ = 16ULL;
v___x_706_ = lean_uint64_shift_right(v_fold_704_, v___x_705_);
v___x_707_ = lean_uint64_xor(v_fold_704_, v___x_706_);
v___x_708_ = lean_uint64_to_usize(v___x_707_);
v___x_709_ = lean_usize_of_nat(v___x_700_);
v___x_710_ = ((size_t)1ULL);
v___x_711_ = lean_usize_sub(v___x_709_, v___x_710_);
v___x_712_ = lean_usize_land(v___x_708_, v___x_711_);
v_bkt_713_ = lean_array_uget_borrowed(v_buckets_696_, v___x_712_);
v___x_714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_694_, v_bkt_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v_size_x27_716_; lean_object* v___x_717_; lean_object* v_buckets_x27_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_715_ = lean_unsigned_to_nat(1u);
v_size_x27_716_ = lean_nat_add(v_size_695_, v___x_715_);
lean_dec(v_size_695_);
lean_inc(v_bkt_713_);
v___x_717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_717_, 0, v_a_694_);
lean_ctor_set(v___x_717_, 1, v___x_715_);
lean_ctor_set(v___x_717_, 2, v_bkt_713_);
v_buckets_x27_718_ = lean_array_uset(v_buckets_696_, v___x_712_, v___x_717_);
v___x_719_ = lean_unsigned_to_nat(4u);
v___x_720_ = lean_nat_mul(v_size_x27_716_, v___x_719_);
v___x_721_ = lean_unsigned_to_nat(3u);
v___x_722_ = lean_nat_div(v___x_720_, v___x_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_array_get_size(v_buckets_x27_718_);
v___x_724_ = lean_nat_dec_le(v___x_722_, v___x_723_);
lean_dec(v___x_722_);
if (v___x_724_ == 0)
{
lean_object* v_val_725_; lean_object* v___x_727_; 
v_val_725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_718_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_val_725_);
lean_ctor_set(v___x_698_, 0, v_size_x27_716_);
v___x_727_ = v___x_698_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_size_x27_716_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_val_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
else
{
lean_object* v___x_730_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_buckets_x27_718_);
lean_ctor_set(v___x_698_, 0, v_size_x27_716_);
v___x_730_ = v___x_698_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_size_x27_716_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_buckets_x27_718_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v___x_732_; lean_object* v_buckets_x27_733_; lean_object* v_bkt_x27_734_; lean_object* v___y_736_; uint8_t v___x_741_; 
lean_inc(v_bkt_713_);
v___x_732_ = lean_box(0);
v_buckets_x27_733_ = lean_array_uset(v_buckets_696_, v___x_712_, v___x_732_);
lean_inc(v_a_694_);
v_bkt_x27_734_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_694_, v_bkt_713_);
v___x_741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_694_, v_bkt_x27_734_);
lean_dec(v_a_694_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_nat_sub(v_size_695_, v___x_742_);
lean_dec(v_size_695_);
v___y_736_ = v___x_743_;
goto v___jp_735_;
}
else
{
v___y_736_ = v_size_695_;
goto v___jp_735_;
}
v___jp_735_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = lean_array_uset(v_buckets_x27_733_, v___x_712_, v_bkt_x27_734_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_737_);
lean_ctor_set(v___x_698_, 0, v___y_736_);
v___x_739_ = v___x_698_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___y_736_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object* v_coeff_745_, lean_object* v_e_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_767_; 
v___x_749_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_exprToVar___redArg(v_e_746_, v_a_747_);
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_767_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_767_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_767_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_fst_754_; lean_object* v_snd_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_766_; 
v_fst_754_ = lean_ctor_get(v_a_750_, 0);
v_snd_755_ = lean_ctor_get(v_a_750_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_a_750_);
if (v_isSharedCheck_766_ == 0)
{
v___x_757_ = v_a_750_;
v_isShared_758_ = v_isSharedCheck_766_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_snd_755_);
lean_inc(v_fst_754_);
lean_dec(v_a_750_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_766_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(v_coeff_745_, v_fst_754_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_snd_755_);
v___x_761_ = v_reuseFailAlloc_765_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_763_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_761_);
v___x_763_ = v___x_752_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object* v_coeff_768_, lean_object* v_e_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_768_, v_e_769_, v_a_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar(lean_object* v_coeff_773_, lean_object* v_e_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_773_, v_e_774_, v_a_775_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object* v_coeff_782_, lean_object* v_e_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar(v_coeff_782_, v_e_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
return v_res_790_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object* v_00_u03b2_791_, lean_object* v_a_792_, lean_object* v_x_793_){
_start:
{
uint8_t v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_795_, lean_object* v_a_796_, lean_object* v_x_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(v_00_u03b2_795_, v_a_796_, v_x_797_);
lean_dec(v_x_797_);
lean_dec(v_a_796_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object* v_00_u03b2_800_, lean_object* v_data_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_data_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_803_, lean_object* v_i_804_, lean_object* v_source_805_, lean_object* v_target_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v_i_804_, v_source_805_, v_target_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_809_, v_x_810_);
return v___x_811_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_812_; double v___x_813_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = lean_float_of_nat(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_817_, lean_object* v_msg_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_ref_825_; lean_object* v___x_826_; lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_872_; 
v_ref_825_ = lean_ctor_get(v___y_822_, 5);
v___x_826_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_818_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_872_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_872_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_872_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v_traceState_832_; lean_object* v_env_833_; lean_object* v_nextMacroScope_834_; lean_object* v_ngen_835_; lean_object* v_auxDeclNGen_836_; lean_object* v_cache_837_; lean_object* v_messages_838_; lean_object* v_infoState_839_; lean_object* v_snapshotTasks_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_871_; 
v___x_831_ = lean_st_ref_take(v___y_823_);
v_traceState_832_ = lean_ctor_get(v___x_831_, 4);
v_env_833_ = lean_ctor_get(v___x_831_, 0);
v_nextMacroScope_834_ = lean_ctor_get(v___x_831_, 1);
v_ngen_835_ = lean_ctor_get(v___x_831_, 2);
v_auxDeclNGen_836_ = lean_ctor_get(v___x_831_, 3);
v_cache_837_ = lean_ctor_get(v___x_831_, 5);
v_messages_838_ = lean_ctor_get(v___x_831_, 6);
v_infoState_839_ = lean_ctor_get(v___x_831_, 7);
v_snapshotTasks_840_ = lean_ctor_get(v___x_831_, 8);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_871_ == 0)
{
v___x_842_ = v___x_831_;
v_isShared_843_ = v_isSharedCheck_871_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_snapshotTasks_840_);
lean_inc(v_infoState_839_);
lean_inc(v_messages_838_);
lean_inc(v_cache_837_);
lean_inc(v_traceState_832_);
lean_inc(v_auxDeclNGen_836_);
lean_inc(v_ngen_835_);
lean_inc(v_nextMacroScope_834_);
lean_inc(v_env_833_);
lean_dec(v___x_831_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_871_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
uint64_t v_tid_844_; lean_object* v_traces_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_870_; 
v_tid_844_ = lean_ctor_get_uint64(v_traceState_832_, sizeof(void*)*1);
v_traces_845_ = lean_ctor_get(v_traceState_832_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v_traceState_832_);
if (v_isSharedCheck_870_ == 0)
{
v___x_847_ = v_traceState_832_;
v_isShared_848_ = v_isSharedCheck_870_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_traces_845_);
lean_dec(v_traceState_832_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_870_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; double v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_849_ = lean_box(0);
v___x_850_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
v___x_851_ = 0;
v___x_852_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_853_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_853_, 0, v_cls_817_);
lean_ctor_set(v___x_853_, 1, v___x_849_);
lean_ctor_set(v___x_853_, 2, v___x_852_);
lean_ctor_set_float(v___x_853_, sizeof(void*)*3, v___x_850_);
lean_ctor_set_float(v___x_853_, sizeof(void*)*3 + 8, v___x_850_);
lean_ctor_set_uint8(v___x_853_, sizeof(void*)*3 + 16, v___x_851_);
v___x_854_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2));
v___x_855_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v_a_827_);
lean_ctor_set(v___x_855_, 2, v___x_854_);
lean_inc(v_ref_825_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_ref_825_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = l_Lean_PersistentArray_push___redArg(v_traces_845_, v___x_856_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_857_);
v___x_859_ = v___x_847_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_857_);
lean_ctor_set_uint64(v_reuseFailAlloc_869_, sizeof(void*)*1, v_tid_844_);
v___x_859_ = v_reuseFailAlloc_869_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_861_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v___x_859_);
v___x_861_ = v___x_842_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_env_833_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_nextMacroScope_834_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_ngen_835_);
lean_ctor_set(v_reuseFailAlloc_868_, 3, v_auxDeclNGen_836_);
lean_ctor_set(v_reuseFailAlloc_868_, 4, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_868_, 5, v_cache_837_);
lean_ctor_set(v_reuseFailAlloc_868_, 6, v_messages_838_);
lean_ctor_set(v_reuseFailAlloc_868_, 7, v_infoState_839_);
lean_ctor_set(v_reuseFailAlloc_868_, 8, v_snapshotTasks_840_);
v___x_861_ = v_reuseFailAlloc_868_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_862_ = lean_st_ref_set(v___y_823_, v___x_861_);
v___x_863_ = lean_box(0);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___y_819_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_864_);
v___x_866_ = v___x_829_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_873_, lean_object* v_msg_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_873_, v_msg_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_881_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6(void){
_start:
{
lean_object* v_cls_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_cls_892_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_893_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_894_ = l_Lean_Name_append(v___x_893_, v_cls_892_);
return v___x_894_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7));
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__13));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_907_, lean_object* v_coeff_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
if (lean_obj_tag(v_a_909_) == 5)
{
lean_object* v_fn_916_; 
v_fn_916_ = lean_ctor_get(v_a_909_, 0);
if (lean_obj_tag(v_fn_916_) == 5)
{
lean_object* v_arg_917_; lean_object* v_fn_918_; lean_object* v_arg_919_; uint8_t v___x_920_; 
v_arg_917_ = lean_ctor_get(v_a_909_, 1);
v_fn_918_ = lean_ctor_get(v_fn_916_, 0);
v_arg_919_ = lean_ctor_get(v_fn_916_, 1);
lean_inc_ref(v_fn_918_);
v___x_920_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg(v_fn_918_);
if (v___x_920_ == 0)
{
lean_object* v_options_921_; uint8_t v_hasTrace_922_; 
v_options_921_ = lean_ctor_get(v_a_913_, 2);
v_hasTrace_922_ = lean_ctor_get_uint8(v_options_921_, sizeof(void*)*1);
if (v_hasTrace_922_ == 0)
{
lean_object* v___x_923_; 
lean_dec_ref(v_op_907_);
v___x_923_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_a_910_);
return v___x_923_;
}
else
{
lean_object* v_inheritedTraceOptions_924_; lean_object* v_cls_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_inheritedTraceOptions_924_ = lean_ctor_get(v_a_913_, 13);
v_cls_925_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_926_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_927_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_924_, v_options_921_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
lean_dec_ref(v_op_907_);
v___x_928_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_a_910_);
return v___x_928_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_929_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_918_);
v___x_930_ = l_Lean_MessageData_ofExpr(v_fn_918_);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
lean_inc_ref(v_arg_919_);
v___x_934_ = l_Lean_MessageData_ofExpr(v_arg_919_);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_932_);
lean_inc_ref(v_arg_917_);
v___x_937_ = l_Lean_MessageData_ofExpr(v_arg_917_);
v___x_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_op_907_);
v___x_942_ = l_Lean_MessageData_ofExpr(v___x_941_);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_940_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_925_, v___x_945_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v_snd_948_; lean_object* v___x_949_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref(v___x_946_);
v_snd_948_ = lean_ctor_get(v_a_947_, 1);
lean_inc(v_snd_948_);
lean_dec(v_a_947_);
v___x_949_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_snd_948_);
return v___x_949_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v_a_909_);
lean_dec_ref(v_coeff_908_);
v_a_950_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_946_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_946_);
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
else
{
lean_object* v___x_958_; 
lean_inc_ref(v_arg_919_);
lean_inc_ref(v_arg_917_);
lean_dec_ref(v_a_909_);
lean_inc_ref(v_op_907_);
v___x_958_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(v_op_907_, v_coeff_908_, v_arg_919_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref(v___x_958_);
v_fst_960_ = lean_ctor_get(v_a_959_, 0);
lean_inc(v_fst_960_);
v_snd_961_ = lean_ctor_get(v_a_959_, 1);
lean_inc(v_snd_961_);
lean_dec(v_a_959_);
v_coeff_908_ = v_fst_960_;
v_a_909_ = v_arg_917_;
v_a_910_ = v_snd_961_;
goto _start;
}
else
{
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_op_907_);
return v___x_958_;
}
}
}
else
{
lean_object* v___x_963_; 
lean_dec_ref(v_op_907_);
v___x_963_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_a_910_);
return v___x_963_;
}
}
else
{
lean_object* v___x_964_; 
lean_dec_ref(v_op_907_);
v___x_964_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_a_910_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_965_, lean_object* v_coeff_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(v_op_965_, v_coeff_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
return v_res_974_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_box(0);
v___x_976_ = lean_unsigned_to_nat(16u);
v___x_977_ = lean_mk_array(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___x_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(lean_object* v_op_981_, lean_object* v_e_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_990_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(v_op_981_, v___x_989_, v_e_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_991_, lean_object* v_e_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_op_991_, v_e_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1000_, lean_object* v_a_1001_, lean_object* v_x_1002_){
_start:
{
if (lean_obj_tag(v_x_1002_) == 0)
{
lean_dec(v_a_1001_);
return v_x_1002_;
}
else
{
lean_object* v_key_1003_; lean_object* v_value_1004_; lean_object* v_tail_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1018_; 
v_key_1003_ = lean_ctor_get(v_x_1002_, 0);
v_value_1004_ = lean_ctor_get(v_x_1002_, 1);
v_tail_1005_ = lean_ctor_get(v_x_1002_, 2);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_x_1002_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1007_ = v_x_1002_;
v_isShared_1008_ = v_isSharedCheck_1018_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_tail_1005_);
lean_inc(v_value_1004_);
lean_inc(v_key_1003_);
lean_dec(v_x_1002_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1018_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
uint8_t v___x_1009_; 
v___x_1009_ = lean_nat_dec_eq(v_key_1003_, v_a_1001_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1000_, v_a_1001_, v_tail_1005_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 2, v___x_1010_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_key_1003_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_value_1004_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_dec(v_key_1003_);
v___x_1014_ = lean_nat_sub(v_value_1004_, v_commonCnt_1000_);
lean_dec(v_value_1004_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v___x_1014_);
lean_ctor_set(v___x_1007_, 0, v_a_1001_);
v___x_1016_ = v___x_1007_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1001_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_tail_1005_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1019_, lean_object* v_a_1020_, lean_object* v_x_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1019_, v_a_1020_, v_x_1021_);
lean_dec(v_commonCnt_1019_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1023_, lean_object* v_m_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_size_1026_; lean_object* v_buckets_1027_; lean_object* v___x_1028_; uint64_t v___x_1029_; uint64_t v___x_1030_; uint64_t v___x_1031_; uint64_t v_fold_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v_bucket_1041_; uint8_t v___x_1042_; 
v_size_1026_ = lean_ctor_get(v_m_1024_, 0);
v_buckets_1027_ = lean_ctor_get(v_m_1024_, 1);
v___x_1028_ = lean_array_get_size(v_buckets_1027_);
v___x_1029_ = lean_uint64_of_nat(v_a_1025_);
v___x_1030_ = 32ULL;
v___x_1031_ = lean_uint64_shift_right(v___x_1029_, v___x_1030_);
v_fold_1032_ = lean_uint64_xor(v___x_1029_, v___x_1031_);
v___x_1033_ = 16ULL;
v___x_1034_ = lean_uint64_shift_right(v_fold_1032_, v___x_1033_);
v___x_1035_ = lean_uint64_xor(v_fold_1032_, v___x_1034_);
v___x_1036_ = lean_uint64_to_usize(v___x_1035_);
v___x_1037_ = lean_usize_of_nat(v___x_1028_);
v___x_1038_ = ((size_t)1ULL);
v___x_1039_ = lean_usize_sub(v___x_1037_, v___x_1038_);
v___x_1040_ = lean_usize_land(v___x_1036_, v___x_1039_);
v_bucket_1041_ = lean_array_uget_borrowed(v_buckets_1027_, v___x_1040_);
v___x_1042_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1025_, v_bucket_1041_);
if (v___x_1042_ == 0)
{
lean_dec(v_a_1025_);
return v_m_1024_;
}
else
{
lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1053_; 
lean_inc(v_bucket_1041_);
lean_inc_ref(v_buckets_1027_);
lean_inc(v_size_1026_);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_m_1024_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; lean_object* v_unused_1055_; 
v_unused_1054_ = lean_ctor_get(v_m_1024_, 1);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v_m_1024_, 0);
lean_dec(v_unused_1055_);
v___x_1044_ = v_m_1024_;
v_isShared_1045_ = v_isSharedCheck_1053_;
goto v_resetjp_1043_;
}
else
{
lean_dec(v_m_1024_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1053_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v_buckets_1047_; lean_object* v_bucket_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1046_ = lean_box(0);
v_buckets_1047_ = lean_array_uset(v_buckets_1027_, v___x_1040_, v___x_1046_);
v_bucket_1048_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1023_, v_a_1025_, v_bucket_1041_);
v___x_1049_ = lean_array_uset(v_buckets_1047_, v___x_1040_, v_bucket_1048_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 1, v___x_1049_);
v___x_1051_ = v___x_1044_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_size_1026_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1056_, lean_object* v_m_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1056_, v_m_1057_, v_a_1058_);
lean_dec(v_commonCnt_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
if (lean_obj_tag(v_x_1061_) == 0)
{
return v_x_1060_;
}
else
{
lean_object* v_key_1062_; lean_object* v_value_1063_; lean_object* v_tail_1064_; lean_object* v___x_1065_; 
v_key_1062_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_key_1062_);
v_value_1063_ = lean_ctor_get(v_x_1061_, 1);
lean_inc(v_value_1063_);
v_tail_1064_ = lean_ctor_get(v_x_1061_, 2);
lean_inc(v_tail_1064_);
lean_dec_ref(v_x_1061_);
v___x_1065_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(v_value_1063_, v_x_1060_, v_key_1062_);
lean_dec(v_value_1063_);
v_x_1060_ = v___x_1065_;
v_x_1061_ = v_tail_1064_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1067_, lean_object* v_x_1068_){
_start:
{
if (lean_obj_tag(v_x_1068_) == 0)
{
return v_x_1067_;
}
else
{
lean_object* v_key_1069_; lean_object* v_value_1070_; lean_object* v_tail_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_key_1069_ = lean_ctor_get(v_x_1068_, 0);
lean_inc(v_key_1069_);
v_value_1070_ = lean_ctor_get(v_x_1068_, 1);
lean_inc(v_value_1070_);
v_tail_1071_ = lean_ctor_get(v_x_1068_, 2);
lean_inc(v_tail_1071_);
lean_dec_ref(v_x_1068_);
v___x_1072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(v_value_1070_, v_x_1067_, v_key_1069_);
lean_dec(v_value_1070_);
v___x_1073_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1072_, v_tail_1071_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1074_, size_t v_i_1075_, size_t v_stop_1076_, lean_object* v_b_1077_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_eq(v_i_1075_, v_stop_1076_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; 
v___x_1079_ = lean_array_uget_borrowed(v_as_1074_, v_i_1075_);
lean_inc(v___x_1079_);
v___x_1080_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1(v_b_1077_, v___x_1079_);
v___x_1081_ = ((size_t)1ULL);
v___x_1082_ = lean_usize_add(v_i_1075_, v___x_1081_);
v_i_1075_ = v___x_1082_;
v_b_1077_ = v___x_1080_;
goto _start;
}
else
{
return v_b_1077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1084_, lean_object* v_i_1085_, lean_object* v_stop_1086_, lean_object* v_b_1087_){
_start:
{
size_t v_i_boxed_1088_; size_t v_stop_boxed_1089_; lean_object* v_res_1090_; 
v_i_boxed_1088_ = lean_unbox_usize(v_i_1085_);
lean_dec(v_i_1085_);
v_stop_boxed_1089_ = lean_unbox_usize(v_stop_1086_);
lean_dec(v_stop_1086_);
v_res_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_as_1084_, v_i_boxed_1088_, v_stop_boxed_1089_, v_b_1087_);
lean_dec_ref(v_as_1084_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1091_, lean_object* v_x_1092_){
_start:
{
if (lean_obj_tag(v_x_1092_) == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_box(0);
return v___x_1093_;
}
else
{
lean_object* v_key_1094_; lean_object* v_value_1095_; lean_object* v_tail_1096_; uint8_t v___x_1097_; 
v_key_1094_ = lean_ctor_get(v_x_1092_, 0);
v_value_1095_ = lean_ctor_get(v_x_1092_, 1);
v_tail_1096_ = lean_ctor_get(v_x_1092_, 2);
v___x_1097_ = lean_nat_dec_eq(v_key_1094_, v_a_1091_);
if (v___x_1097_ == 0)
{
v_x_1092_ = v_tail_1096_;
goto _start;
}
else
{
lean_object* v___x_1099_; 
lean_inc(v_value_1095_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_value_1095_);
return v___x_1099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1100_, lean_object* v_x_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1100_, v_x_1101_);
lean_dec(v_x_1101_);
lean_dec(v_a_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_buckets_1105_; lean_object* v___x_1106_; uint64_t v___x_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; uint64_t v_fold_1110_; uint64_t v___x_1111_; uint64_t v___x_1112_; uint64_t v___x_1113_; size_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_buckets_1105_ = lean_ctor_get(v_m_1103_, 1);
v___x_1106_ = lean_array_get_size(v_buckets_1105_);
v___x_1107_ = lean_uint64_of_nat(v_a_1104_);
v___x_1108_ = 32ULL;
v___x_1109_ = lean_uint64_shift_right(v___x_1107_, v___x_1108_);
v_fold_1110_ = lean_uint64_xor(v___x_1107_, v___x_1109_);
v___x_1111_ = 16ULL;
v___x_1112_ = lean_uint64_shift_right(v_fold_1110_, v___x_1111_);
v___x_1113_ = lean_uint64_xor(v_fold_1110_, v___x_1112_);
v___x_1114_ = lean_uint64_to_usize(v___x_1113_);
v___x_1115_ = lean_usize_of_nat(v___x_1106_);
v___x_1116_ = ((size_t)1ULL);
v___x_1117_ = lean_usize_sub(v___x_1115_, v___x_1116_);
v___x_1118_ = lean_usize_land(v___x_1114_, v___x_1117_);
v___x_1119_ = lean_array_uget_borrowed(v_buckets_1105_, v___x_1118_);
v___x_1120_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1104_, v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_m_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1124_, lean_object* v_b_1125_, lean_object* v_x_1126_){
_start:
{
if (lean_obj_tag(v_x_1126_) == 0)
{
lean_dec(v_b_1125_);
lean_dec(v_a_1124_);
return v_x_1126_;
}
else
{
lean_object* v_key_1127_; lean_object* v_value_1128_; lean_object* v_tail_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1141_; 
v_key_1127_ = lean_ctor_get(v_x_1126_, 0);
v_value_1128_ = lean_ctor_get(v_x_1126_, 1);
v_tail_1129_ = lean_ctor_get(v_x_1126_, 2);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_x_1126_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1131_ = v_x_1126_;
v_isShared_1132_ = v_isSharedCheck_1141_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_tail_1129_);
lean_inc(v_value_1128_);
lean_inc(v_key_1127_);
lean_dec(v_x_1126_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1141_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_nat_dec_eq(v_key_1127_, v_a_1124_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1124_, v_b_1125_, v_tail_1129_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 2, v___x_1134_);
v___x_1136_ = v___x_1131_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_key_1127_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_value_1128_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
else
{
lean_object* v___x_1139_; 
lean_dec(v_value_1128_);
lean_dec(v_key_1127_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v_b_1125_);
lean_ctor_set(v___x_1131_, 0, v_a_1124_);
v___x_1139_ = v___x_1131_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1124_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_b_1125_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_tail_1129_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1142_, lean_object* v_a_1143_, lean_object* v_b_1144_){
_start:
{
lean_object* v_size_1145_; lean_object* v_buckets_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1189_; 
v_size_1145_ = lean_ctor_get(v_m_1142_, 0);
v_buckets_1146_ = lean_ctor_get(v_m_1142_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_m_1142_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1148_ = v_m_1142_;
v_isShared_1149_ = v_isSharedCheck_1189_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_buckets_1146_);
lean_inc(v_size_1145_);
lean_dec(v_m_1142_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1189_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; uint64_t v___x_1151_; uint64_t v___x_1152_; uint64_t v___x_1153_; uint64_t v_fold_1154_; uint64_t v___x_1155_; uint64_t v___x_1156_; uint64_t v___x_1157_; size_t v___x_1158_; size_t v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; lean_object* v_bkt_1163_; uint8_t v___x_1164_; 
v___x_1150_ = lean_array_get_size(v_buckets_1146_);
v___x_1151_ = lean_uint64_of_nat(v_a_1143_);
v___x_1152_ = 32ULL;
v___x_1153_ = lean_uint64_shift_right(v___x_1151_, v___x_1152_);
v_fold_1154_ = lean_uint64_xor(v___x_1151_, v___x_1153_);
v___x_1155_ = 16ULL;
v___x_1156_ = lean_uint64_shift_right(v_fold_1154_, v___x_1155_);
v___x_1157_ = lean_uint64_xor(v_fold_1154_, v___x_1156_);
v___x_1158_ = lean_uint64_to_usize(v___x_1157_);
v___x_1159_ = lean_usize_of_nat(v___x_1150_);
v___x_1160_ = ((size_t)1ULL);
v___x_1161_ = lean_usize_sub(v___x_1159_, v___x_1160_);
v___x_1162_ = lean_usize_land(v___x_1158_, v___x_1161_);
v_bkt_1163_ = lean_array_uget_borrowed(v_buckets_1146_, v___x_1162_);
v___x_1164_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1143_, v_bkt_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v_size_x27_1166_; lean_object* v___x_1167_; lean_object* v_buckets_x27_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1165_ = lean_unsigned_to_nat(1u);
v_size_x27_1166_ = lean_nat_add(v_size_1145_, v___x_1165_);
lean_dec(v_size_1145_);
lean_inc(v_bkt_1163_);
v___x_1167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1167_, 0, v_a_1143_);
lean_ctor_set(v___x_1167_, 1, v_b_1144_);
lean_ctor_set(v___x_1167_, 2, v_bkt_1163_);
v_buckets_x27_1168_ = lean_array_uset(v_buckets_1146_, v___x_1162_, v___x_1167_);
v___x_1169_ = lean_unsigned_to_nat(4u);
v___x_1170_ = lean_nat_mul(v_size_x27_1166_, v___x_1169_);
v___x_1171_ = lean_unsigned_to_nat(3u);
v___x_1172_ = lean_nat_div(v___x_1170_, v___x_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_array_get_size(v_buckets_x27_1168_);
v___x_1174_ = lean_nat_dec_le(v___x_1172_, v___x_1173_);
lean_dec(v___x_1172_);
if (v___x_1174_ == 0)
{
lean_object* v_val_1175_; lean_object* v___x_1177_; 
v_val_1175_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1168_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_val_1175_);
lean_ctor_set(v___x_1148_, 0, v_size_x27_1166_);
v___x_1177_ = v___x_1148_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_size_x27_1166_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_val_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
else
{
lean_object* v___x_1180_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_buckets_x27_1168_);
lean_ctor_set(v___x_1148_, 0, v_size_x27_1166_);
v___x_1180_ = v___x_1148_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_size_x27_1166_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_buckets_x27_1168_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
lean_object* v___x_1182_; lean_object* v_buckets_x27_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
lean_inc(v_bkt_1163_);
v___x_1182_ = lean_box(0);
v_buckets_x27_1183_ = lean_array_uset(v_buckets_1146_, v___x_1162_, v___x_1182_);
v___x_1184_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1143_, v_b_1144_, v_bkt_1163_);
v___x_1185_ = lean_array_uset(v_buckets_x27_1183_, v___x_1162_, v___x_1184_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v___x_1185_);
v___x_1187_ = v___x_1148_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_size_1145_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
return v_x_1191_;
}
else
{
lean_object* v_key_1193_; lean_object* v_value_1194_; lean_object* v_tail_1195_; lean_object* v___y_1197_; lean_object* v___x_1200_; 
v_key_1193_ = lean_ctor_get(v_x_1192_, 0);
lean_inc(v_key_1193_);
v_value_1194_ = lean_ctor_get(v_x_1192_, 1);
lean_inc(v_value_1194_);
v_tail_1195_ = lean_ctor_get(v_x_1192_, 2);
lean_inc(v_tail_1195_);
lean_dec_ref(v_x_1192_);
v___x_1200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1190_, v_key_1193_);
if (lean_obj_tag(v___x_1200_) == 1)
{
lean_object* v_val_1201_; uint8_t v___x_1202_; 
v_val_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_val_1201_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = lean_nat_dec_le(v_value_1194_, v_val_1201_);
if (v___x_1202_ == 0)
{
lean_dec(v_value_1194_);
v___y_1197_ = v_val_1201_;
goto v___jp_1196_;
}
else
{
lean_dec(v_val_1201_);
v___y_1197_ = v_value_1194_;
goto v___jp_1196_;
}
}
else
{
lean_dec(v___x_1200_);
lean_dec(v_value_1194_);
lean_dec(v_key_1193_);
v_x_1192_ = v_tail_1195_;
goto _start;
}
v___jp_1196_:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1191_, v_key_1193_, v___y_1197_);
v_x_1191_ = v___x_1198_;
v_x_1192_ = v_tail_1195_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(v_snd_1204_, v_x_1205_, v_x_1206_);
lean_dec_ref(v_snd_1204_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1208_, lean_object* v_as_1209_, size_t v_i_1210_, size_t v_stop_1211_, lean_object* v_b_1212_){
_start:
{
uint8_t v___x_1213_; 
v___x_1213_ = lean_usize_dec_eq(v_i_1210_, v_stop_1211_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; 
v___x_1214_ = lean_array_uget_borrowed(v_as_1209_, v_i_1210_);
lean_inc(v___x_1214_);
v___x_1215_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(v_snd_1208_, v_b_1212_, v___x_1214_);
v___x_1216_ = ((size_t)1ULL);
v___x_1217_ = lean_usize_add(v_i_1210_, v___x_1216_);
v_i_1210_ = v___x_1217_;
v_b_1212_ = v___x_1215_;
goto _start;
}
else
{
return v_b_1212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1219_, lean_object* v_as_1220_, lean_object* v_i_1221_, lean_object* v_stop_1222_, lean_object* v_b_1223_){
_start:
{
size_t v_i_boxed_1224_; size_t v_stop_boxed_1225_; lean_object* v_res_1226_; 
v_i_boxed_1224_ = lean_unbox_usize(v_i_1221_);
lean_dec(v_i_1221_);
v_stop_boxed_1225_ = lean_unbox_usize(v_stop_1222_);
lean_dec(v_stop_1222_);
v_res_1226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(v_snd_1219_, v_as_1220_, v_i_boxed_1224_, v_stop_boxed_1225_, v_b_1223_);
lean_dec_ref(v_as_1220_);
lean_dec_ref(v_snd_1219_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1227_, lean_object* v_y_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v___y_1232_; lean_object* v_fst_1233_; lean_object* v_snd_1234_; lean_object* v_size_1238_; lean_object* v_buckets_1239_; lean_object* v_size_1240_; lean_object* v_buckets_1241_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1248_; lean_object* v_buckets_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v_buckets_1266_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v_fst_1283_; lean_object* v_buckets_1284_; lean_object* v_snd_1285_; uint8_t v___x_1298_; 
v_size_1238_ = lean_ctor_get(v_y_1228_, 0);
lean_inc(v_size_1238_);
v_buckets_1239_ = lean_ctor_get(v_y_1228_, 1);
v_size_1240_ = lean_ctor_get(v_x_1227_, 0);
lean_inc(v_size_1240_);
v_buckets_1241_ = lean_ctor_get(v_x_1227_, 1);
v___x_1298_ = lean_nat_dec_lt(v_size_1238_, v_size_1240_);
if (v___x_1298_ == 0)
{
lean_inc_ref(v_buckets_1241_);
v_fst_1283_ = v_x_1227_;
v_buckets_1284_ = v_buckets_1241_;
v_snd_1285_ = v_y_1228_;
goto v___jp_1282_;
}
else
{
lean_inc_ref(v_buckets_1239_);
v_fst_1283_ = v_y_1228_;
v_buckets_1284_ = v_buckets_1239_;
v_snd_1285_ = v_x_1227_;
goto v___jp_1282_;
}
v___jp_1231_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1235_, 0, v___y_1232_);
lean_ctor_set(v___x_1235_, 1, v_fst_1233_);
lean_ctor_set(v___x_1235_, 2, v_snd_1234_);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v_a_1229_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
v___jp_1242_:
{
uint8_t v___x_1246_; 
v___x_1246_ = lean_nat_dec_lt(v_size_1238_, v_size_1240_);
lean_dec(v_size_1240_);
lean_dec(v_size_1238_);
if (v___x_1246_ == 0)
{
v___y_1232_ = v___y_1243_;
v_fst_1233_ = v___y_1244_;
v_snd_1234_ = v___y_1245_;
goto v___jp_1231_;
}
else
{
v___y_1232_ = v___y_1243_;
v_fst_1233_ = v___y_1245_;
v_snd_1234_ = v___y_1244_;
goto v___jp_1231_;
}
}
v___jp_1247_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = lean_array_get_size(v_buckets_1249_);
v___x_1254_ = lean_nat_dec_lt(v___x_1252_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_dec_ref(v_buckets_1249_);
v___y_1243_ = v___y_1248_;
v___y_1244_ = v___y_1251_;
v___y_1245_ = v___y_1250_;
goto v___jp_1242_;
}
else
{
uint8_t v___x_1255_; 
v___x_1255_ = lean_nat_dec_le(v___x_1253_, v___x_1253_);
if (v___x_1255_ == 0)
{
if (v___x_1254_ == 0)
{
lean_dec_ref(v_buckets_1249_);
v___y_1243_ = v___y_1248_;
v___y_1244_ = v___y_1251_;
v___y_1245_ = v___y_1250_;
goto v___jp_1242_;
}
else
{
size_t v___x_1256_; size_t v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = ((size_t)0ULL);
v___x_1257_ = lean_usize_of_nat(v___x_1253_);
v___x_1258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1249_, v___x_1256_, v___x_1257_, v___y_1250_);
lean_dec_ref(v_buckets_1249_);
v___y_1243_ = v___y_1248_;
v___y_1244_ = v___y_1251_;
v___y_1245_ = v___x_1258_;
goto v___jp_1242_;
}
}
else
{
size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = ((size_t)0ULL);
v___x_1260_ = lean_usize_of_nat(v___x_1253_);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1249_, v___x_1259_, v___x_1260_, v___y_1250_);
lean_dec_ref(v_buckets_1249_);
v___y_1243_ = v___y_1248_;
v___y_1244_ = v___y_1251_;
v___y_1245_ = v___x_1261_;
goto v___jp_1242_;
}
}
}
v___jp_1262_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_array_get_size(v_buckets_1266_);
v___x_1269_ = lean_nat_dec_lt(v___x_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
v___y_1248_ = v___y_1265_;
v_buckets_1249_ = v_buckets_1266_;
v___y_1250_ = v___y_1264_;
v___y_1251_ = v___y_1263_;
goto v___jp_1247_;
}
else
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_nat_dec_le(v___x_1268_, v___x_1268_);
if (v___x_1270_ == 0)
{
if (v___x_1269_ == 0)
{
v___y_1248_ = v___y_1265_;
v_buckets_1249_ = v_buckets_1266_;
v___y_1250_ = v___y_1264_;
v___y_1251_ = v___y_1263_;
goto v___jp_1247_;
}
else
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = lean_usize_of_nat(v___x_1268_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1266_, v___x_1271_, v___x_1272_, v___y_1263_);
v___y_1248_ = v___y_1265_;
v_buckets_1249_ = v_buckets_1266_;
v___y_1250_ = v___y_1264_;
v___y_1251_ = v___x_1273_;
goto v___jp_1247_;
}
}
else
{
size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = lean_usize_of_nat(v___x_1268_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1266_, v___x_1274_, v___x_1275_, v___y_1263_);
v___y_1248_ = v___y_1265_;
v_buckets_1249_ = v_buckets_1266_;
v___y_1250_ = v___y_1264_;
v___y_1251_ = v___x_1276_;
goto v___jp_1247_;
}
}
}
v___jp_1277_:
{
lean_object* v_buckets_1281_; 
v_buckets_1281_ = lean_ctor_get(v___y_1280_, 1);
lean_inc_ref(v_buckets_1281_);
v___y_1263_ = v___y_1278_;
v___y_1264_ = v___y_1279_;
v___y_1265_ = v___y_1280_;
v_buckets_1266_ = v_buckets_1281_;
goto v___jp_1262_;
}
v___jp_1282_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1286_ = lean_unsigned_to_nat(0u);
v___x_1287_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1288_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1289_ = lean_array_get_size(v_buckets_1284_);
v___x_1290_ = lean_nat_dec_lt(v___x_1286_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_dec_ref(v_buckets_1284_);
v___y_1263_ = v_fst_1283_;
v___y_1264_ = v_snd_1285_;
v___y_1265_ = v___x_1288_;
v_buckets_1266_ = v___x_1287_;
goto v___jp_1262_;
}
else
{
uint8_t v___x_1291_; 
v___x_1291_ = lean_nat_dec_le(v___x_1289_, v___x_1289_);
if (v___x_1291_ == 0)
{
if (v___x_1290_ == 0)
{
lean_dec_ref(v_buckets_1284_);
v___y_1263_ = v_fst_1283_;
v___y_1264_ = v_snd_1285_;
v___y_1265_ = v___x_1288_;
v_buckets_1266_ = v___x_1287_;
goto v___jp_1262_;
}
else
{
size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = ((size_t)0ULL);
v___x_1293_ = lean_usize_of_nat(v___x_1289_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(v_snd_1285_, v_buckets_1284_, v___x_1292_, v___x_1293_, v___x_1288_);
lean_dec_ref(v_buckets_1284_);
v___y_1278_ = v_fst_1283_;
v___y_1279_ = v_snd_1285_;
v___y_1280_ = v___x_1294_;
goto v___jp_1277_;
}
}
else
{
size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
v___x_1295_ = ((size_t)0ULL);
v___x_1296_ = lean_usize_of_nat(v___x_1289_);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(v_snd_1285_, v_buckets_1284_, v___x_1295_, v___x_1296_, v___x_1288_);
lean_dec_ref(v_buckets_1284_);
v___y_1278_ = v_fst_1283_;
v___y_1279_ = v_snd_1285_;
v___y_1280_ = v___x_1297_;
goto v___jp_1277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1299_, lean_object* v_y_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_x_1299_, v_y_1300_, v_a_1301_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute(lean_object* v_x_1304_, lean_object* v_y_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_x_1304_, v_y_1305_, v_a_1306_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1313_, lean_object* v_y_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute(v_x_1313_, v_y_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1322_, lean_object* v_m_1323_, lean_object* v_a_1324_, lean_object* v_b_1325_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1323_, v_a_1324_, v_b_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1327_, lean_object* v_m_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1328_, v_a_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1331_, lean_object* v_m_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1331_, v_m_1332_, v_a_1333_);
lean_dec(v_a_1333_);
lean_dec_ref(v_m_1332_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1335_, lean_object* v_a_1336_, lean_object* v_b_1337_, lean_object* v_x_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1336_, v_b_1337_, v_x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1340_, lean_object* v_a_1341_, lean_object* v_x_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1341_, v_x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1344_, lean_object* v_a_1345_, lean_object* v_x_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1344_, v_a_1345_, v_x_1346_);
lean_dec(v_x_1346_);
lean_dec(v_a_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object* v_hi_1348_, lean_object* v_pivot_1349_, lean_object* v_as_1350_, lean_object* v_i_1351_, lean_object* v_k_1352_){
_start:
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_nat_dec_lt(v_k_1352_, v_hi_1348_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec(v_k_1352_);
v___x_1354_ = lean_array_fswap(v_as_1350_, v_i_1351_, v_hi_1348_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_i_1351_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
return v___x_1355_;
}
else
{
lean_object* v___x_1356_; lean_object* v_fst_1357_; lean_object* v_fst_1358_; uint8_t v___x_1359_; 
v___x_1356_ = lean_array_fget_borrowed(v_as_1350_, v_k_1352_);
v_fst_1357_ = lean_ctor_get(v___x_1356_, 0);
v_fst_1358_ = lean_ctor_get(v_pivot_1349_, 0);
v___x_1359_ = lean_nat_dec_lt(v_fst_1357_, v_fst_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_unsigned_to_nat(1u);
v___x_1361_ = lean_nat_add(v_k_1352_, v___x_1360_);
lean_dec(v_k_1352_);
v_k_1352_ = v___x_1361_;
goto _start;
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1363_ = lean_array_fswap(v_as_1350_, v_i_1351_, v_k_1352_);
v___x_1364_ = lean_unsigned_to_nat(1u);
v___x_1365_ = lean_nat_add(v_i_1351_, v___x_1364_);
lean_dec(v_i_1351_);
v___x_1366_ = lean_nat_add(v_k_1352_, v___x_1364_);
lean_dec(v_k_1352_);
v_as_1350_ = v___x_1363_;
v_i_1351_ = v___x_1365_;
v_k_1352_ = v___x_1366_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object* v_hi_1368_, lean_object* v_pivot_1369_, lean_object* v_as_1370_, lean_object* v_i_1371_, lean_object* v_k_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1368_, v_pivot_1369_, v_as_1370_, v_i_1371_, v_k_1372_);
lean_dec_ref(v_pivot_1369_);
lean_dec(v_hi_1368_);
return v_res_1373_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1374_, lean_object* v_x2_1375_){
_start:
{
lean_object* v_fst_1376_; lean_object* v_fst_1377_; uint8_t v___x_1378_; 
v_fst_1376_ = lean_ctor_get(v_x1_1374_, 0);
v_fst_1377_ = lean_ctor_get(v_x2_1375_, 0);
v___x_1378_ = lean_nat_dec_lt(v_fst_1376_, v_fst_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1379_, lean_object* v_x2_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1379_, v_x2_1380_);
lean_dec_ref(v_x2_1380_);
lean_dec_ref(v_x1_1379_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_n_1383_, lean_object* v_as_1384_, lean_object* v_lo_1385_, lean_object* v_hi_1386_){
_start:
{
lean_object* v___y_1388_; uint8_t v___x_1398_; 
v___x_1398_ = lean_nat_dec_lt(v_lo_1385_, v_hi_1386_);
if (v___x_1398_ == 0)
{
lean_dec(v_lo_1385_);
return v_as_1384_;
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v_mid_1401_; lean_object* v___y_1403_; lean_object* v___y_1409_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1399_ = lean_nat_add(v_lo_1385_, v_hi_1386_);
v___x_1400_ = lean_unsigned_to_nat(1u);
v_mid_1401_ = lean_nat_shiftr(v___x_1399_, v___x_1400_);
lean_dec(v___x_1399_);
v___x_1414_ = lean_array_fget_borrowed(v_as_1384_, v_mid_1401_);
v___x_1415_ = lean_array_fget_borrowed(v_as_1384_, v_lo_1385_);
v___x_1416_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
v___y_1409_ = v_as_1384_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_array_fswap(v_as_1384_, v_lo_1385_, v_mid_1401_);
v___y_1409_ = v___x_1417_;
goto v___jp_1408_;
}
v___jp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1404_ = lean_array_fget_borrowed(v___y_1403_, v_mid_1401_);
v___x_1405_ = lean_array_fget_borrowed(v___y_1403_, v_hi_1386_);
v___x_1406_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_dec(v_mid_1401_);
v___y_1388_ = v___y_1403_;
goto v___jp_1387_;
}
else
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_array_fswap(v___y_1403_, v_mid_1401_, v_hi_1386_);
lean_dec(v_mid_1401_);
v___y_1388_ = v___x_1407_;
goto v___jp_1387_;
}
}
v___jp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1410_ = lean_array_fget_borrowed(v___y_1409_, v_hi_1386_);
v___x_1411_ = lean_array_fget_borrowed(v___y_1409_, v_lo_1385_);
v___x_1412_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
v___y_1403_ = v___y_1409_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_array_fswap(v___y_1409_, v_lo_1385_, v_hi_1386_);
v___y_1403_ = v___x_1413_;
goto v___jp_1402_;
}
}
}
v___jp_1387_:
{
lean_object* v_pivot_1389_; lean_object* v___x_1390_; lean_object* v_fst_1391_; lean_object* v_snd_1392_; uint8_t v___x_1393_; 
v_pivot_1389_ = lean_array_fget(v___y_1388_, v_hi_1386_);
lean_inc_n(v_lo_1385_, 2);
v___x_1390_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1386_, v_pivot_1389_, v___y_1388_, v_lo_1385_, v_lo_1385_);
lean_dec(v_pivot_1389_);
v_fst_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_fst_1391_);
v_snd_1392_ = lean_ctor_get(v___x_1390_, 1);
lean_inc(v_snd_1392_);
lean_dec_ref(v___x_1390_);
v___x_1393_ = lean_nat_dec_le(v_hi_1386_, v_fst_1391_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1383_, v_snd_1392_, v_lo_1385_, v_fst_1391_);
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = lean_nat_add(v_fst_1391_, v___x_1395_);
lean_dec(v_fst_1391_);
v_as_1384_ = v___x_1394_;
v_lo_1385_ = v___x_1396_;
goto _start;
}
else
{
lean_dec(v_fst_1391_);
lean_dec(v_lo_1385_);
return v_snd_1392_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_n_1418_, lean_object* v_as_1419_, lean_object* v_lo_1420_, lean_object* v_hi_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1418_, v_as_1419_, v_lo_1420_, v_hi_1421_);
lean_dec(v_hi_1421_);
lean_dec(v_n_1418_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1423_, lean_object* v___x_1424_, lean_object* v_op_1425_, lean_object* v_a_1426_, lean_object* v_b_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___y_1431_; uint8_t v___x_1435_; 
v___x_1435_ = lean_nat_dec_lt(v_a_1426_, v_upperBound_1423_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec(v_a_1426_);
lean_dec_ref(v_op_1425_);
lean_dec_ref(v___x_1424_);
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_b_1427_);
lean_ctor_set(v___x_1436_, 1, v___y_1428_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
return v___x_1437_;
}
else
{
if (lean_obj_tag(v_b_1427_) == 0)
{
lean_object* v___x_1438_; 
lean_inc_ref(v___x_1424_);
v___x_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1424_);
v___y_1431_ = v___x_1438_;
goto v___jp_1430_;
}
else
{
lean_object* v_val_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1448_; 
v_val_1439_ = lean_ctor_get(v_b_1427_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_b_1427_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1441_ = v_b_1427_;
v_isShared_1442_ = v_isSharedCheck_1448_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_val_1439_);
lean_dec(v_b_1427_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1448_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_inc_ref(v_op_1425_);
v___x_1443_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_op_1425_);
lean_inc_ref(v___x_1424_);
v___x_1444_ = l_Lean_mkAppB(v___x_1443_, v_val_1439_, v___x_1424_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1444_);
v___x_1446_ = v___x_1441_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
v___y_1431_ = v___x_1446_;
goto v___jp_1430_;
}
}
}
}
v___jp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_unsigned_to_nat(1u);
v___x_1433_ = lean_nat_add(v_a_1426_, v___x_1432_);
lean_dec(v_a_1426_);
v_a_1426_ = v___x_1433_;
v_b_1427_ = v___y_1431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1449_, lean_object* v___x_1450_, lean_object* v_op_1451_, lean_object* v_a_1452_, lean_object* v_b_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1449_, v___x_1450_, v_op_1451_, v_a_1452_, v_b_1453_, v___y_1454_);
lean_dec(v_upperBound_1449_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1457_, lean_object* v_as_1458_, size_t v_sz_1459_, size_t v_i_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v___x_1468_; 
v___x_1468_ = lean_usize_dec_lt(v_i_1460_, v_sz_1459_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec_ref(v_op_1457_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v_b_1461_);
lean_ctor_set(v___x_1469_, 1, v___y_1462_);
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
else
{
lean_object* v_a_1471_; lean_object* v_fst_1472_; lean_object* v_snd_1473_; lean_object* v_varToExpr_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_a_1471_ = lean_array_uget_borrowed(v_as_1458_, v_i_1460_);
v_fst_1472_ = lean_ctor_get(v_a_1471_, 0);
v_snd_1473_ = lean_ctor_get(v_a_1471_, 1);
v_varToExpr_1474_ = lean_ctor_get(v___y_1462_, 2);
v___x_1475_ = l_Lean_instInhabitedExpr;
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_array_get(v___x_1475_, v_varToExpr_1474_, v_fst_1472_);
lean_inc_ref(v_op_1457_);
v___x_1478_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1473_, v___x_1477_, v_op_1457_, v___x_1476_, v_b_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v_fst_1480_; lean_object* v_snd_1481_; size_t v___x_1482_; size_t v___x_1483_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref(v___x_1478_);
v_fst_1480_ = lean_ctor_get(v_a_1479_, 0);
lean_inc(v_fst_1480_);
v_snd_1481_ = lean_ctor_get(v_a_1479_, 1);
lean_inc(v_snd_1481_);
lean_dec(v_a_1479_);
v___x_1482_ = ((size_t)1ULL);
v___x_1483_ = lean_usize_add(v_i_1460_, v___x_1482_);
v_i_1460_ = v___x_1483_;
v_b_1461_ = v_fst_1480_;
v___y_1462_ = v_snd_1481_;
goto _start;
}
else
{
lean_dec_ref(v_op_1457_);
return v___x_1478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1485_, lean_object* v_as_1486_, lean_object* v_sz_1487_, lean_object* v_i_1488_, lean_object* v_b_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
size_t v_sz_boxed_1496_; size_t v_i_boxed_1497_; lean_object* v_res_1498_; 
v_sz_boxed_1496_ = lean_unbox_usize(v_sz_1487_);
lean_dec(v_sz_1487_);
v_i_boxed_1497_ = lean_unbox_usize(v_i_1488_);
lean_dec(v_i_1488_);
v_res_1498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1485_, v_as_1486_, v_sz_boxed_1496_, v_i_boxed_1497_, v_b_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec_ref(v_as_1486_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
if (lean_obj_tag(v_x_1500_) == 0)
{
return v_x_1499_;
}
else
{
lean_object* v_key_1501_; lean_object* v_value_1502_; lean_object* v_tail_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_key_1501_ = lean_ctor_get(v_x_1500_, 0);
v_value_1502_ = lean_ctor_get(v_x_1500_, 1);
v_tail_1503_ = lean_ctor_get(v_x_1500_, 2);
lean_inc(v_value_1502_);
lean_inc(v_key_1501_);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v_key_1501_);
lean_ctor_set(v___x_1504_, 1, v_value_1502_);
v___x_1505_ = lean_array_push(v_x_1499_, v___x_1504_);
v_x_1499_ = v___x_1505_;
v_x_1500_ = v_tail_1503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1507_, lean_object* v_x_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1507_, v_x_1508_);
lean_dec(v_x_1508_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1510_, size_t v_i_1511_, size_t v_stop_1512_, lean_object* v_b_1513_){
_start:
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_usize_dec_eq(v_i_1511_, v_stop_1512_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; size_t v___x_1517_; size_t v___x_1518_; 
v___x_1515_ = lean_array_uget_borrowed(v_as_1510_, v_i_1511_);
v___x_1516_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1513_, v___x_1515_);
v___x_1517_ = ((size_t)1ULL);
v___x_1518_ = lean_usize_add(v_i_1511_, v___x_1517_);
v_i_1511_ = v___x_1518_;
v_b_1513_ = v___x_1516_;
goto _start;
}
else
{
return v_b_1513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1520_, lean_object* v_i_1521_, lean_object* v_stop_1522_, lean_object* v_b_1523_){
_start:
{
size_t v_i_boxed_1524_; size_t v_stop_boxed_1525_; lean_object* v_res_1526_; 
v_i_boxed_1524_ = lean_unbox_usize(v_i_1521_);
lean_dec(v_i_1521_);
v_stop_boxed_1525_ = lean_unbox_usize(v_stop_1522_);
lean_dec(v_stop_1522_);
v_res_1526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1520_, v_i_boxed_1524_, v_stop_boxed_1525_, v_b_1523_);
lean_dec_ref(v_as_1520_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1527_, lean_object* v_op_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v___y_1536_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1554_; lean_object* v_size_1561_; lean_object* v_buckets_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v_size_1561_ = lean_ctor_get(v_coeff_1527_, 0);
v_buckets_1562_ = lean_ctor_get(v_coeff_1527_, 1);
v___x_1563_ = lean_mk_empty_array_with_capacity(v_size_1561_);
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = lean_array_get_size(v_buckets_1562_);
v___x_1566_ = lean_nat_dec_lt(v___x_1564_, v___x_1565_);
if (v___x_1566_ == 0)
{
v___y_1554_ = v___x_1563_;
goto v___jp_1553_;
}
else
{
uint8_t v___x_1567_; 
v___x_1567_ = lean_nat_dec_le(v___x_1565_, v___x_1565_);
if (v___x_1567_ == 0)
{
if (v___x_1566_ == 0)
{
v___y_1554_ = v___x_1563_;
goto v___jp_1553_;
}
else
{
size_t v___x_1568_; size_t v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = ((size_t)0ULL);
v___x_1569_ = lean_usize_of_nat(v___x_1565_);
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1562_, v___x_1568_, v___x_1569_, v___x_1563_);
v___y_1554_ = v___x_1570_;
goto v___jp_1553_;
}
}
else
{
size_t v___x_1571_; size_t v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = ((size_t)0ULL);
v___x_1572_ = lean_usize_of_nat(v___x_1565_);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1562_, v___x_1571_, v___x_1572_, v___x_1563_);
v___y_1554_ = v___x_1573_;
goto v___jp_1553_;
}
}
v___jp_1535_:
{
lean_object* v_acc_1537_; size_t v_sz_1538_; size_t v___x_1539_; lean_object* v___x_1540_; 
v_acc_1537_ = lean_box(0);
v_sz_1538_ = lean_array_size(v___y_1536_);
v___x_1539_ = ((size_t)0ULL);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1528_, v___y_1536_, v_sz_1538_, v___x_1539_, v_acc_1537_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec_ref(v___y_1536_);
return v___x_1540_;
}
v___jp_1541_:
{
lean_object* v___x_1546_; 
v___x_1546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1544_, v___y_1542_, v___y_1543_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec(v___y_1544_);
v___y_1536_ = v___x_1546_;
goto v___jp_1535_;
}
v___jp_1547_:
{
uint8_t v___x_1552_; 
v___x_1552_ = lean_nat_dec_le(v___y_1551_, v___y_1549_);
if (v___x_1552_ == 0)
{
lean_dec(v___y_1549_);
lean_inc(v___y_1551_);
v___y_1542_ = v___y_1548_;
v___y_1543_ = v___y_1551_;
v___y_1544_ = v___y_1550_;
v___y_1545_ = v___y_1551_;
goto v___jp_1541_;
}
else
{
v___y_1542_ = v___y_1548_;
v___y_1543_ = v___y_1551_;
v___y_1544_ = v___y_1550_;
v___y_1545_ = v___y_1549_;
goto v___jp_1541_;
}
}
v___jp_1553_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1555_ = lean_array_get_size(v___y_1554_);
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = lean_nat_dec_eq(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1558_ = lean_unsigned_to_nat(1u);
v___x_1559_ = lean_nat_sub(v___x_1555_, v___x_1558_);
v___x_1560_ = lean_nat_dec_le(v___x_1556_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_inc(v___x_1559_);
v___y_1548_ = v___y_1554_;
v___y_1549_ = v___x_1559_;
v___y_1550_ = v___x_1555_;
v___y_1551_ = v___x_1559_;
goto v___jp_1547_;
}
else
{
v___y_1548_ = v___y_1554_;
v___y_1549_ = v___x_1559_;
v___y_1550_ = v___x_1555_;
v___y_1551_ = v___x_1556_;
goto v___jp_1547_;
}
}
else
{
v___y_1536_ = v___y_1554_;
goto v___jp_1535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1574_, lean_object* v_op_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_coeff_1574_, v_op_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec_ref(v_coeff_1574_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1583_, lean_object* v___x_1584_, lean_object* v_op_1585_, lean_object* v_inst_1586_, lean_object* v_R_1587_, lean_object* v_a_1588_, lean_object* v_b_1589_, lean_object* v_c_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1583_, v___x_1584_, v_op_1585_, v_a_1588_, v_b_1589_, v___y_1591_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1598_, lean_object* v___x_1599_, lean_object* v_op_1600_, lean_object* v_inst_1601_, lean_object* v_R_1602_, lean_object* v_a_1603_, lean_object* v_b_1604_, lean_object* v_c_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1598_, v___x_1599_, v_op_1600_, v_inst_1601_, v_R_1602_, v_a_1603_, v_b_1604_, v_c_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v_upperBound_1598_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1613_, lean_object* v_as_1614_, lean_object* v_lo_1615_, lean_object* v_hi_1616_, lean_object* v_w_1617_, lean_object* v_hlo_1618_, lean_object* v_hhi_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1613_, v_as_1614_, v_lo_1615_, v_hi_1616_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1621_, lean_object* v_as_1622_, lean_object* v_lo_1623_, lean_object* v_hi_1624_, lean_object* v_w_1625_, lean_object* v_hlo_1626_, lean_object* v_hhi_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1621_, v_as_1622_, v_lo_1623_, v_hi_1624_, v_w_1625_, v_hlo_1626_, v_hhi_1627_);
lean_dec(v_hi_1624_);
lean_dec(v_n_1621_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object* v_n_1629_, lean_object* v_lo_1630_, lean_object* v_hi_1631_, lean_object* v_hhi_1632_, lean_object* v_pivot_1633_, lean_object* v_as_1634_, lean_object* v_i_1635_, lean_object* v_k_1636_, lean_object* v_ilo_1637_, lean_object* v_ik_1638_, lean_object* v_w_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1631_, v_pivot_1633_, v_as_1634_, v_i_1635_, v_k_1636_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object* v_n_1641_, lean_object* v_lo_1642_, lean_object* v_hi_1643_, lean_object* v_hhi_1644_, lean_object* v_pivot_1645_, lean_object* v_as_1646_, lean_object* v_i_1647_, lean_object* v_k_1648_, lean_object* v_ilo_1649_, lean_object* v_ik_1650_, lean_object* v_w_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_n_1641_, v_lo_1642_, v_hi_1643_, v_hhi_1644_, v_pivot_1645_, v_as_1646_, v_i_1647_, v_k_1648_, v_ilo_1649_, v_ik_1650_, v_w_1651_);
lean_dec_ref(v_pivot_1645_);
lean_dec(v_hi_1643_);
lean_dec(v_lo_1642_);
lean_dec(v_n_1641_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1653_, lean_object* v___y_1654_){
_start:
{
uint8_t v___x_1656_; 
v___x_1656_ = l_Lean_Expr_hasMVar(v_e_1653_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v_e_1653_);
return v___x_1657_;
}
else
{
lean_object* v___x_1658_; lean_object* v_mctx_1659_; lean_object* v___x_1660_; lean_object* v_fst_1661_; lean_object* v_snd_1662_; lean_object* v___x_1663_; lean_object* v_cache_1664_; lean_object* v_zetaDeltaFVarIds_1665_; lean_object* v_postponed_1666_; lean_object* v_diag_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1676_; 
v___x_1658_ = lean_st_ref_get(v___y_1654_);
v_mctx_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc_ref(v_mctx_1659_);
lean_dec(v___x_1658_);
v___x_1660_ = l_Lean_instantiateMVarsCore(v_mctx_1659_, v_e_1653_);
v_fst_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_fst_1661_);
v_snd_1662_ = lean_ctor_get(v___x_1660_, 1);
lean_inc(v_snd_1662_);
lean_dec_ref(v___x_1660_);
v___x_1663_ = lean_st_ref_take(v___y_1654_);
v_cache_1664_ = lean_ctor_get(v___x_1663_, 1);
v_zetaDeltaFVarIds_1665_ = lean_ctor_get(v___x_1663_, 2);
v_postponed_1666_ = lean_ctor_get(v___x_1663_, 3);
v_diag_1667_ = lean_ctor_get(v___x_1663_, 4);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v___x_1663_, 0);
lean_dec(v_unused_1677_);
v___x_1669_ = v___x_1663_;
v_isShared_1670_ = v_isSharedCheck_1676_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_diag_1667_);
lean_inc(v_postponed_1666_);
lean_inc(v_zetaDeltaFVarIds_1665_);
lean_inc(v_cache_1664_);
lean_dec(v___x_1663_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1676_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v_snd_1662_);
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_snd_1662_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_cache_1664_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_zetaDeltaFVarIds_1665_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v_postponed_1666_);
lean_ctor_set(v_reuseFailAlloc_1675_, 4, v_diag_1667_);
v___x_1672_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_st_ref_set(v___y_1654_, v___x_1672_);
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_fst_1661_);
return v___x_1674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1678_, v___y_1679_);
lean_dec(v___y_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1682_, v___y_1684_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0(v_e_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(lean_object* v_x_1696_, lean_object* v_y_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_Meta_mkEq(v_x_1696_, v_y_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1726_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1726_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1726_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 1);
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
uint8_t v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = 0;
v___x_1711_ = lean_box(0);
v___x_1712_ = l_Lean_Meta_mkFreshExprMVar(v___x_1709_, v___x_1710_, v___x_1711_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref(v___x_1712_);
v___x_1714_ = l_Lean_Expr_mvarId_x21(v_a_1713_);
v___x_1715_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1714_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v___x_1716_; 
lean_dec_ref(v___x_1715_);
v___x_1716_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1713_, v_a_1699_);
return v___x_1716_;
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_a_1713_);
v_a_1717_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1715_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1715_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
else
{
return v___x_1712_;
}
}
}
}
else
{
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1727_, lean_object* v_y_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(v_x_1727_, v_y_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
return v_res_1734_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = lean_unsigned_to_nat(32u);
v___x_1736_ = lean_mk_empty_array_with_capacity(v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1738_ = ((size_t)5ULL);
v___x_1739_ = lean_unsigned_to_nat(0u);
v___x_1740_ = lean_unsigned_to_nat(32u);
v___x_1741_ = lean_mk_empty_array_with_capacity(v___x_1740_);
v___x_1742_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1743_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v___x_1741_);
lean_ctor_set(v___x_1743_, 2, v___x_1739_);
lean_ctor_set(v___x_1743_, 3, v___x_1739_);
lean_ctor_set_usize(v___x_1743_, 4, v___x_1738_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; lean_object* v_traceState_1747_; lean_object* v_traces_1748_; lean_object* v___x_1749_; lean_object* v_traceState_1750_; lean_object* v_env_1751_; lean_object* v_nextMacroScope_1752_; lean_object* v_ngen_1753_; lean_object* v_auxDeclNGen_1754_; lean_object* v_cache_1755_; lean_object* v_messages_1756_; lean_object* v_infoState_1757_; lean_object* v_snapshotTasks_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1777_; 
v___x_1746_ = lean_st_ref_get(v___y_1744_);
v_traceState_1747_ = lean_ctor_get(v___x_1746_, 4);
lean_inc_ref(v_traceState_1747_);
lean_dec(v___x_1746_);
v_traces_1748_ = lean_ctor_get(v_traceState_1747_, 0);
lean_inc_ref(v_traces_1748_);
lean_dec_ref(v_traceState_1747_);
v___x_1749_ = lean_st_ref_take(v___y_1744_);
v_traceState_1750_ = lean_ctor_get(v___x_1749_, 4);
v_env_1751_ = lean_ctor_get(v___x_1749_, 0);
v_nextMacroScope_1752_ = lean_ctor_get(v___x_1749_, 1);
v_ngen_1753_ = lean_ctor_get(v___x_1749_, 2);
v_auxDeclNGen_1754_ = lean_ctor_get(v___x_1749_, 3);
v_cache_1755_ = lean_ctor_get(v___x_1749_, 5);
v_messages_1756_ = lean_ctor_get(v___x_1749_, 6);
v_infoState_1757_ = lean_ctor_get(v___x_1749_, 7);
v_snapshotTasks_1758_ = lean_ctor_get(v___x_1749_, 8);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1760_ = v___x_1749_;
v_isShared_1761_ = v_isSharedCheck_1777_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_snapshotTasks_1758_);
lean_inc(v_infoState_1757_);
lean_inc(v_messages_1756_);
lean_inc(v_cache_1755_);
lean_inc(v_traceState_1750_);
lean_inc(v_auxDeclNGen_1754_);
lean_inc(v_ngen_1753_);
lean_inc(v_nextMacroScope_1752_);
lean_inc(v_env_1751_);
lean_dec(v___x_1749_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1777_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
uint64_t v_tid_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1775_; 
v_tid_1762_ = lean_ctor_get_uint64(v_traceState_1750_, sizeof(void*)*1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_traceState_1750_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v_traceState_1750_, 0);
lean_dec(v_unused_1776_);
v___x_1764_ = v_traceState_1750_;
v_isShared_1765_ = v_isSharedCheck_1775_;
goto v_resetjp_1763_;
}
else
{
lean_dec(v_traceState_1750_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1775_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1766_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1766_);
v___x_1768_ = v___x_1764_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1766_);
lean_ctor_set_uint64(v_reuseFailAlloc_1774_, sizeof(void*)*1, v_tid_1762_);
v___x_1768_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1770_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 4, v___x_1768_);
v___x_1770_ = v___x_1760_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_env_1751_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_nextMacroScope_1752_);
lean_ctor_set(v_reuseFailAlloc_1773_, 2, v_ngen_1753_);
lean_ctor_set(v_reuseFailAlloc_1773_, 3, v_auxDeclNGen_1754_);
lean_ctor_set(v_reuseFailAlloc_1773_, 4, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1773_, 5, v_cache_1755_);
lean_ctor_set(v_reuseFailAlloc_1773_, 6, v_messages_1756_);
lean_ctor_set(v_reuseFailAlloc_1773_, 7, v_infoState_1757_);
lean_ctor_set(v_reuseFailAlloc_1773_, 8, v_snapshotTasks_1758_);
v___x_1770_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_st_ref_set(v___y_1744_, v___x_1770_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v_traces_1748_);
return v___x_1772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1778_);
lean_dec(v___y_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1787_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1(v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
return v_res_1798_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1799_, lean_object* v_opt_1800_){
_start:
{
lean_object* v_name_1801_; lean_object* v_defValue_1802_; lean_object* v_map_1803_; lean_object* v___x_1804_; 
v_name_1801_ = lean_ctor_get(v_opt_1800_, 0);
v_defValue_1802_ = lean_ctor_get(v_opt_1800_, 1);
v_map_1803_ = lean_ctor_get(v_opts_1799_, 0);
v___x_1804_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1803_, v_name_1801_);
if (lean_obj_tag(v___x_1804_) == 0)
{
uint8_t v___x_1805_; 
v___x_1805_ = lean_unbox(v_defValue_1802_);
return v___x_1805_;
}
else
{
lean_object* v_val_1806_; 
v_val_1806_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_val_1806_);
lean_dec_ref(v___x_1804_);
if (lean_obj_tag(v_val_1806_) == 1)
{
uint8_t v_v_1807_; 
v_v_1807_ = lean_ctor_get_uint8(v_val_1806_, 0);
lean_dec_ref(v_val_1806_);
return v_v_1807_;
}
else
{
uint8_t v___x_1808_; 
lean_dec(v_val_1806_);
v___x_1808_ = lean_unbox(v_defValue_1802_);
return v___x_1808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1809_, lean_object* v_opt_1810_){
_start:
{
uint8_t v_res_1811_; lean_object* v_r_1812_; 
v_res_1811_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_opts_1809_, v_opt_1810_);
lean_dec_ref(v_opt_1810_);
lean_dec_ref(v_opts_1809_);
v_r_1812_ = lean_box(v_res_1811_);
return v_r_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1813_, lean_object* v_____do__lift_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_options_1823_; uint8_t v_hasTrace_1824_; 
v_options_1823_ = lean_ctor_get(v___y_1820_, 2);
v_hasTrace_1824_ = lean_ctor_get_uint8(v_options_1823_, sizeof(void*)*1);
if (v_hasTrace_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_dec(v_cls_1813_);
v___x_1825_ = lean_box(v_hasTrace_1824_);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1828_ = l_Lean_Name_append(v___x_1827_, v_cls_1813_);
v___x_1829_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1814_, v_options_1823_, v___x_1828_);
lean_dec(v___x_1828_);
v___x_1830_ = lean_box(v___x_1829_);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1832_, lean_object* v_____do__lift_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_1832_, v_____do__lift_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v_____do__lift_1833_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_mkAppB(v___x_1843_, v___y_1844_, v___y_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1847_, lean_object* v_lhs_1848_, lean_object* v_rhs_1849_, lean_object* v_P_1850_, uint8_t v___x_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; 
lean_inc_ref(v_lhs_1848_);
lean_inc_ref(v_val_1847_);
v___x_1858_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_1847_, v_lhs_1848_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v_fst_1860_; lean_object* v_snd_1861_; lean_object* v___x_1862_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1858_);
v_fst_1860_ = lean_ctor_get(v_a_1859_, 0);
lean_inc(v_fst_1860_);
v_snd_1861_ = lean_ctor_get(v_a_1859_, 1);
lean_inc(v_snd_1861_);
lean_dec(v_a_1859_);
lean_inc_ref(v_rhs_1849_);
lean_inc_ref(v_val_1847_);
v___x_1862_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_1847_, v_rhs_1849_, v_snd_1861_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v_fst_1864_; lean_object* v_snd_1865_; lean_object* v___x_1866_; lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1957_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref(v___x_1862_);
v_fst_1864_ = lean_ctor_get(v_a_1863_, 0);
lean_inc(v_fst_1864_);
v_snd_1865_ = lean_ctor_get(v_a_1863_, 1);
lean_inc(v_snd_1865_);
lean_dec(v_a_1863_);
v___x_1866_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_fst_1860_, v_fst_1864_, v_snd_1865_);
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1957_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1957_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v_fst_1871_; lean_object* v_snd_1872_; lean_object* v_common_1873_; lean_object* v_x_1874_; lean_object* v_y_1875_; lean_object* v___x_1876_; 
v_fst_1871_ = lean_ctor_get(v_a_1867_, 0);
lean_inc(v_fst_1871_);
v_snd_1872_ = lean_ctor_get(v_a_1867_, 1);
lean_inc(v_snd_1872_);
lean_dec(v_a_1867_);
v_common_1873_ = lean_ctor_get(v_fst_1871_, 0);
lean_inc_ref(v_common_1873_);
v_x_1874_ = lean_ctor_get(v_fst_1871_, 1);
lean_inc_ref(v_x_1874_);
v_y_1875_ = lean_ctor_get(v_fst_1871_, 2);
lean_inc_ref(v_y_1875_);
lean_dec(v_fst_1871_);
lean_inc_ref(v_val_1847_);
v___x_1876_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_common_1873_, v_val_1847_, v_snd_1872_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec_ref(v_common_1873_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v_fst_1878_; lean_object* v_snd_1879_; lean_object* v___x_1880_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1876_);
v_fst_1878_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_fst_1878_);
v_snd_1879_ = lean_ctor_get(v_a_1877_, 1);
lean_inc(v_snd_1879_);
lean_dec(v_a_1877_);
lean_inc_ref(v_val_1847_);
v___x_1880_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_x_1874_, v_val_1847_, v_snd_1879_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec_ref(v_x_1874_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_fst_1882_; lean_object* v_snd_1883_; lean_object* v___x_1884_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1880_);
v_fst_1882_ = lean_ctor_get(v_a_1881_, 0);
lean_inc(v_fst_1882_);
v_snd_1883_ = lean_ctor_get(v_a_1881_, 1);
lean_inc(v_snd_1883_);
lean_dec(v_a_1881_);
lean_inc_ref(v_val_1847_);
v___x_1884_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_y_1875_, v_val_1847_, v_snd_1883_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec_ref(v_y_1875_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v_fst_1886_; lean_object* v_snd_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1932_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
v_fst_1886_ = lean_ctor_get(v_a_1885_, 0);
v_snd_1887_ = lean_ctor_get(v_a_1885_, 1);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_a_1885_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1889_ = v_a_1885_;
v_isShared_1890_ = v_isSharedCheck_1932_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_snd_1887_);
lean_inc(v_fst_1886_);
lean_dec(v_a_1885_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1932_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___x_1922_; lean_object* v___f_1923_; lean_object* v___y_1925_; lean_object* v___x_1929_; 
lean_inc_ref(v_val_1847_);
v___x_1922_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_1847_);
v___f_1923_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_1923_, 0, v___x_1922_);
lean_inc(v_fst_1878_);
lean_inc_ref(v___f_1923_);
v___x_1929_ = l_Option_merge___redArg(v___f_1923_, v_fst_1878_, v_fst_1882_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v___x_1930_; 
lean_inc_ref(v_val_1847_);
v___x_1930_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_1847_);
v___y_1925_ = v___x_1930_;
goto v___jp_1924_;
}
else
{
lean_object* v_val_1931_; 
v_val_1931_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_val_1931_);
lean_dec_ref(v___x_1929_);
v___y_1925_ = v_val_1931_;
goto v___jp_1924_;
}
v___jp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_inc_ref(v_P_1850_);
v___x_1894_ = l_Lean_mkAppB(v_P_1850_, v_lhs_1848_, v_rhs_1849_);
v___x_1895_ = l_Lean_mkAppB(v_P_1850_, v___y_1892_, v___y_1893_);
lean_inc_ref(v___x_1895_);
v___x_1896_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(v___x_1894_, v___x_1895_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1913_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1913_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1913_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 1);
lean_ctor_set(v___x_1869_, 0, v_a_1897_);
v___x_1902_ = v___x_1869_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1903_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1903_, 0, v___x_1895_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
lean_ctor_set_uint8(v___x_1903_, sizeof(void*)*2, v___x_1851_);
v___x_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
v___x_1905_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1905_);
v___x_1907_ = v___x_1889_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_snd_1887_);
v___x_1907_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1909_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1907_);
v___x_1909_ = v___x_1899_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v___x_1895_);
lean_del_object(v___x_1889_);
lean_dec(v_snd_1887_);
lean_del_object(v___x_1869_);
v_a_1914_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1896_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1896_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
v___jp_1924_:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Option_merge___redArg(v___f_1923_, v_fst_1878_, v_fst_1886_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_1847_);
v___y_1892_ = v___y_1925_;
v___y_1893_ = v___x_1927_;
goto v___jp_1891_;
}
else
{
lean_object* v_val_1928_; 
lean_dec_ref(v_val_1847_);
v_val_1928_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_val_1928_);
lean_dec_ref(v___x_1926_);
v___y_1892_ = v___y_1925_;
v___y_1893_ = v_val_1928_;
goto v___jp_1891_;
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_fst_1882_);
lean_dec(v_fst_1878_);
lean_del_object(v___x_1869_);
lean_dec_ref(v_P_1850_);
lean_dec_ref(v_rhs_1849_);
lean_dec_ref(v_lhs_1848_);
lean_dec_ref(v_val_1847_);
v_a_1933_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1884_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1884_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v_fst_1878_);
lean_dec_ref(v_y_1875_);
lean_del_object(v___x_1869_);
lean_dec_ref(v_P_1850_);
lean_dec_ref(v_rhs_1849_);
lean_dec_ref(v_lhs_1848_);
lean_dec_ref(v_val_1847_);
v_a_1941_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1880_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1880_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_y_1875_);
lean_dec_ref(v_x_1874_);
lean_del_object(v___x_1869_);
lean_dec_ref(v_P_1850_);
lean_dec_ref(v_rhs_1849_);
lean_dec_ref(v_lhs_1848_);
lean_dec_ref(v_val_1847_);
v_a_1949_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1876_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1876_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_fst_1860_);
lean_dec_ref(v_P_1850_);
lean_dec_ref(v_rhs_1849_);
lean_dec_ref(v_lhs_1848_);
lean_dec_ref(v_val_1847_);
v_a_1958_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1862_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1862_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v_P_1850_);
lean_dec_ref(v_rhs_1849_);
lean_dec_ref(v_lhs_1848_);
lean_dec_ref(v_val_1847_);
v_a_1966_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1858_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1858_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_1974_, lean_object* v_lhs_1975_, lean_object* v_rhs_1976_, lean_object* v_P_1977_, lean_object* v___x_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
uint8_t v___x_118078__boxed_1985_; lean_object* v_res_1986_; 
v___x_118078__boxed_1985_ = lean_unbox(v___x_1978_);
v_res_1986_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2(v_val_1974_, v_lhs_1975_, v_rhs_1976_, v_P_1977_, v___x_118078__boxed_1985_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
return v_res_1986_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_1989_ = l_Lean_stringToMessageData(v___x_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(v_x_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v_x_2001_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5(lean_object* v_val_2011_, lean_object* v_lhs_2012_, lean_object* v_rhs_2013_, lean_object* v_P_2014_, uint8_t v_hasTrace_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; 
lean_inc_ref(v_lhs_2012_);
lean_inc_ref(v_val_2011_);
v___x_2022_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_2011_, v_lhs_2012_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v_fst_2024_; lean_object* v_snd_2025_; lean_object* v___x_2026_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref(v___x_2022_);
v_fst_2024_ = lean_ctor_get(v_a_2023_, 0);
lean_inc(v_fst_2024_);
v_snd_2025_ = lean_ctor_get(v_a_2023_, 1);
lean_inc(v_snd_2025_);
lean_dec(v_a_2023_);
lean_inc_ref(v_rhs_2013_);
lean_inc_ref(v_val_2011_);
v___x_2026_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_2011_, v_rhs_2013_, v_snd_2025_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v___x_2030_; lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2121_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_2026_);
v_fst_2028_ = lean_ctor_get(v_a_2027_, 0);
lean_inc(v_fst_2028_);
v_snd_2029_ = lean_ctor_get(v_a_2027_, 1);
lean_inc(v_snd_2029_);
lean_dec(v_a_2027_);
v___x_2030_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_fst_2024_, v_fst_2028_, v_snd_2029_);
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2121_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2121_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v_fst_2035_; lean_object* v_snd_2036_; lean_object* v_common_2037_; lean_object* v_x_2038_; lean_object* v_y_2039_; lean_object* v___x_2040_; 
v_fst_2035_ = lean_ctor_get(v_a_2031_, 0);
lean_inc(v_fst_2035_);
v_snd_2036_ = lean_ctor_get(v_a_2031_, 1);
lean_inc(v_snd_2036_);
lean_dec(v_a_2031_);
v_common_2037_ = lean_ctor_get(v_fst_2035_, 0);
lean_inc_ref(v_common_2037_);
v_x_2038_ = lean_ctor_get(v_fst_2035_, 1);
lean_inc_ref(v_x_2038_);
v_y_2039_ = lean_ctor_get(v_fst_2035_, 2);
lean_inc_ref(v_y_2039_);
lean_dec(v_fst_2035_);
lean_inc_ref(v_val_2011_);
v___x_2040_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_common_2037_, v_val_2011_, v_snd_2036_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec_ref(v_common_2037_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v_fst_2042_; lean_object* v_snd_2043_; lean_object* v___x_2044_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref(v___x_2040_);
v_fst_2042_ = lean_ctor_get(v_a_2041_, 0);
lean_inc(v_fst_2042_);
v_snd_2043_ = lean_ctor_get(v_a_2041_, 1);
lean_inc(v_snd_2043_);
lean_dec(v_a_2041_);
lean_inc_ref(v_val_2011_);
v___x_2044_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_x_2038_, v_val_2011_, v_snd_2043_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec_ref(v_x_2038_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v_fst_2046_; lean_object* v_snd_2047_; lean_object* v___x_2048_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2044_);
v_fst_2046_ = lean_ctor_get(v_a_2045_, 0);
lean_inc(v_fst_2046_);
v_snd_2047_ = lean_ctor_get(v_a_2045_, 1);
lean_inc(v_snd_2047_);
lean_dec(v_a_2045_);
lean_inc_ref(v_val_2011_);
v___x_2048_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_y_2039_, v_val_2011_, v_snd_2047_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec_ref(v_y_2039_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v_fst_2050_; lean_object* v_snd_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2096_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref(v___x_2048_);
v_fst_2050_ = lean_ctor_get(v_a_2049_, 0);
v_snd_2051_ = lean_ctor_get(v_a_2049_, 1);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_a_2049_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2053_ = v_a_2049_;
v_isShared_2054_ = v_isSharedCheck_2096_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_snd_2051_);
lean_inc(v_fst_2050_);
lean_dec(v_a_2049_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2096_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___x_2086_; lean_object* v___f_2087_; lean_object* v___y_2089_; lean_object* v___x_2093_; 
lean_inc_ref(v_val_2011_);
v___x_2086_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2011_);
v___f_2087_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2087_, 0, v___x_2086_);
lean_inc(v_fst_2042_);
lean_inc_ref(v___f_2087_);
v___x_2093_ = l_Option_merge___redArg(v___f_2087_, v_fst_2042_, v_fst_2046_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v___x_2094_; 
lean_inc_ref(v_val_2011_);
v___x_2094_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_2011_);
v___y_2089_ = v___x_2094_;
goto v___jp_2088_;
}
else
{
lean_object* v_val_2095_; 
v_val_2095_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_val_2095_);
lean_dec_ref(v___x_2093_);
v___y_2089_ = v_val_2095_;
goto v___jp_2088_;
}
v___jp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_inc_ref(v_P_2014_);
v___x_2058_ = l_Lean_mkAppB(v_P_2014_, v_lhs_2012_, v_rhs_2013_);
v___x_2059_ = l_Lean_mkAppB(v_P_2014_, v___y_2056_, v___y_2057_);
lean_inc_ref(v___x_2059_);
v___x_2060_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(v___x_2058_, v___x_2059_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2077_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2077_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2077_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 1);
lean_ctor_set(v___x_2033_, 0, v_a_2061_);
v___x_2066_ = v___x_2033_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2067_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2067_, 0, v___x_2059_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*2, v_hasTrace_2015_);
v___x_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2069_);
v___x_2071_ = v___x_2053_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_snd_2051_);
v___x_2071_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2073_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2071_);
v___x_2073_ = v___x_2063_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v___x_2059_);
lean_del_object(v___x_2053_);
lean_dec(v_snd_2051_);
lean_del_object(v___x_2033_);
v_a_2078_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2060_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2060_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
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
v___jp_2088_:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Option_merge___redArg(v___f_2087_, v_fst_2042_, v_fst_2050_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_2011_);
v___y_2056_ = v___y_2089_;
v___y_2057_ = v___x_2091_;
goto v___jp_2055_;
}
else
{
lean_object* v_val_2092_; 
lean_dec_ref(v_val_2011_);
v_val_2092_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_val_2092_);
lean_dec_ref(v___x_2090_);
v___y_2056_ = v___y_2089_;
v___y_2057_ = v_val_2092_;
goto v___jp_2055_;
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_fst_2046_);
lean_dec(v_fst_2042_);
lean_del_object(v___x_2033_);
lean_dec_ref(v_P_2014_);
lean_dec_ref(v_rhs_2013_);
lean_dec_ref(v_lhs_2012_);
lean_dec_ref(v_val_2011_);
v_a_2097_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2048_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2048_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v_fst_2042_);
lean_dec_ref(v_y_2039_);
lean_del_object(v___x_2033_);
lean_dec_ref(v_P_2014_);
lean_dec_ref(v_rhs_2013_);
lean_dec_ref(v_lhs_2012_);
lean_dec_ref(v_val_2011_);
v_a_2105_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2044_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2044_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec_ref(v_y_2039_);
lean_dec_ref(v_x_2038_);
lean_del_object(v___x_2033_);
lean_dec_ref(v_P_2014_);
lean_dec_ref(v_rhs_2013_);
lean_dec_ref(v_lhs_2012_);
lean_dec_ref(v_val_2011_);
v_a_2113_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2040_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2040_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_fst_2024_);
lean_dec_ref(v_P_2014_);
lean_dec_ref(v_rhs_2013_);
lean_dec_ref(v_lhs_2012_);
lean_dec_ref(v_val_2011_);
v_a_2122_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2026_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2026_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec_ref(v_P_2014_);
lean_dec_ref(v_rhs_2013_);
lean_dec_ref(v_lhs_2012_);
lean_dec_ref(v_val_2011_);
v_a_2130_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2022_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2022_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object* v_val_2138_, lean_object* v_lhs_2139_, lean_object* v_rhs_2140_, lean_object* v_P_2141_, lean_object* v_hasTrace_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
uint8_t v_hasTrace_boxed_2149_; lean_object* v_res_2150_; 
v_hasTrace_boxed_2149_ = lean_unbox(v_hasTrace_2142_);
v_res_2150_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5(v_val_2138_, v_lhs_2139_, v_rhs_2140_, v_P_2141_, v_hasTrace_boxed_2149_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2151_, lean_object* v_msg_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_ref_2158_; lean_object* v___x_2159_; lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2204_; 
v_ref_2158_ = lean_ctor_get(v___y_2155_, 5);
v___x_2159_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2204_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2204_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v_traceState_2165_; lean_object* v_env_2166_; lean_object* v_nextMacroScope_2167_; lean_object* v_ngen_2168_; lean_object* v_auxDeclNGen_2169_; lean_object* v_cache_2170_; lean_object* v_messages_2171_; lean_object* v_infoState_2172_; lean_object* v_snapshotTasks_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2203_; 
v___x_2164_ = lean_st_ref_take(v___y_2156_);
v_traceState_2165_ = lean_ctor_get(v___x_2164_, 4);
v_env_2166_ = lean_ctor_get(v___x_2164_, 0);
v_nextMacroScope_2167_ = lean_ctor_get(v___x_2164_, 1);
v_ngen_2168_ = lean_ctor_get(v___x_2164_, 2);
v_auxDeclNGen_2169_ = lean_ctor_get(v___x_2164_, 3);
v_cache_2170_ = lean_ctor_get(v___x_2164_, 5);
v_messages_2171_ = lean_ctor_get(v___x_2164_, 6);
v_infoState_2172_ = lean_ctor_get(v___x_2164_, 7);
v_snapshotTasks_2173_ = lean_ctor_get(v___x_2164_, 8);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2175_ = v___x_2164_;
v_isShared_2176_ = v_isSharedCheck_2203_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_snapshotTasks_2173_);
lean_inc(v_infoState_2172_);
lean_inc(v_messages_2171_);
lean_inc(v_cache_2170_);
lean_inc(v_traceState_2165_);
lean_inc(v_auxDeclNGen_2169_);
lean_inc(v_ngen_2168_);
lean_inc(v_nextMacroScope_2167_);
lean_inc(v_env_2166_);
lean_dec(v___x_2164_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2203_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
uint64_t v_tid_2177_; lean_object* v_traces_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2202_; 
v_tid_2177_ = lean_ctor_get_uint64(v_traceState_2165_, sizeof(void*)*1);
v_traces_2178_ = lean_ctor_get(v_traceState_2165_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_traceState_2165_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2180_ = v_traceState_2165_;
v_isShared_2181_ = v_isSharedCheck_2202_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_traces_2178_);
lean_dec(v_traceState_2165_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2202_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; double v___x_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2182_ = lean_box(0);
v___x_2183_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
v___x_2184_ = 0;
v___x_2185_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_2186_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2186_, 0, v_cls_2151_);
lean_ctor_set(v___x_2186_, 1, v___x_2182_);
lean_ctor_set(v___x_2186_, 2, v___x_2185_);
lean_ctor_set_float(v___x_2186_, sizeof(void*)*3, v___x_2183_);
lean_ctor_set_float(v___x_2186_, sizeof(void*)*3 + 8, v___x_2183_);
lean_ctor_set_uint8(v___x_2186_, sizeof(void*)*3 + 16, v___x_2184_);
v___x_2187_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2));
v___x_2188_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v_a_2160_);
lean_ctor_set(v___x_2188_, 2, v___x_2187_);
lean_inc(v_ref_2158_);
v___x_2189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2189_, 0, v_ref_2158_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_PersistentArray_push___redArg(v_traces_2178_, v___x_2189_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2190_);
v___x_2192_ = v___x_2180_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2190_);
lean_ctor_set_uint64(v_reuseFailAlloc_2201_, sizeof(void*)*1, v_tid_2177_);
v___x_2192_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2194_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 4, v___x_2192_);
v___x_2194_ = v___x_2175_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_env_2166_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_nextMacroScope_2167_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_ngen_2168_);
lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_auxDeclNGen_2169_);
lean_ctor_set(v_reuseFailAlloc_2200_, 4, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2200_, 5, v_cache_2170_);
lean_ctor_set(v_reuseFailAlloc_2200_, 6, v_messages_2171_);
lean_ctor_set(v_reuseFailAlloc_2200_, 7, v_infoState_2172_);
lean_ctor_set(v_reuseFailAlloc_2200_, 8, v_snapshotTasks_2173_);
v___x_2194_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2195_ = lean_st_ref_set(v___y_2156_, v___x_2194_);
v___x_2196_ = lean_box(0);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2196_);
v___x_2198_ = v___x_2162_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2205_, lean_object* v_msg_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2205_, v_msg_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
return v_res_2212_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__1));
v___x_2217_ = l_Lean_stringToMessageData(v___x_2216_);
return v___x_2217_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__3));
v___x_2220_ = l_Lean_stringToMessageData(v___x_2219_);
return v___x_2220_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__5));
v___x_2223_ = l_Lean_stringToMessageData(v___x_2222_);
return v___x_2223_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_unsigned_to_nat(16u);
v___x_2226_ = lean_mk_array(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__7);
v___x_2228_ = lean_unsigned_to_nat(0u);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v___x_2227_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__10));
v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__12));
v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__14));
v___x_2240_ = l_Lean_stringToMessageData(v___x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(lean_object* v_lhs_2241_, lean_object* v_rhs_2242_, lean_object* v___f_2243_, lean_object* v_cls_2244_, uint8_t v___x_2245_, lean_object* v_P_2246_, uint8_t v_hasTrace_2247_, lean_object* v_____r_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v___x_2266_; 
lean_inc_ref(v_lhs_2241_);
v___x_2266_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_lhs_2241_);
if (lean_obj_tag(v___x_2266_) == 1)
{
lean_object* v_val_2267_; lean_object* v___x_2268_; 
v_val_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_val_2267_);
lean_dec_ref(v___x_2266_);
lean_inc_ref(v_rhs_2242_);
v___x_2268_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_rhs_2242_);
if (lean_obj_tag(v___x_2268_) == 1)
{
lean_object* v_val_2269_; uint8_t v___x_2308_; 
v_val_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_val_2269_);
lean_dec_ref(v___x_2268_);
v___x_2308_ = lean_expr_eqv(v_val_2267_, v_val_2269_);
if (v___x_2308_ == 0)
{
lean_dec_ref(v_P_2246_);
goto v___jp_2270_;
}
else
{
if (v___x_2245_ == 0)
{
lean_object* v_options_2309_; lean_object* v_inheritedTraceOptions_2310_; uint8_t v_hasTrace_2311_; lean_object* v___x_2312_; lean_object* v___f_2313_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; 
lean_dec(v_val_2269_);
lean_dec_ref(v___f_2243_);
v_options_2309_ = lean_ctor_get(v___y_2254_, 2);
v_inheritedTraceOptions_2310_ = lean_ctor_get(v___y_2254_, 13);
v_hasTrace_2311_ = lean_ctor_get_uint8(v_options_2309_, sizeof(void*)*1);
v___x_2312_ = lean_box(v_hasTrace_2247_);
lean_inc(v_val_2267_);
v___f_2313_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__5___boxed), 11, 5);
lean_closure_set(v___f_2313_, 0, v_val_2267_);
lean_closure_set(v___f_2313_, 1, v_lhs_2241_);
lean_closure_set(v___f_2313_, 2, v_rhs_2242_);
lean_closure_set(v___f_2313_, 3, v_P_2246_);
lean_closure_set(v___f_2313_, 4, v___x_2312_);
if (v_hasTrace_2311_ == 0)
{
lean_dec(v_cls_2244_);
v___y_2315_ = v___y_2252_;
v___y_2316_ = v___y_2253_;
v___y_2317_ = v___y_2254_;
v___y_2318_ = v___y_2255_;
goto v___jp_2314_;
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2323_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2244_);
v___x_2324_ = l_Lean_Name_append(v___x_2323_, v_cls_2244_);
v___x_2325_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2310_, v_options_2309_, v___x_2324_);
lean_dec(v___x_2324_);
if (v___x_2325_ == 0)
{
lean_dec(v_cls_2244_);
v___y_2315_ = v___y_2252_;
v___y_2316_ = v___y_2253_;
v___y_2317_ = v___y_2254_;
v___y_2318_ = v___y_2255_;
goto v___jp_2314_;
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2326_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11);
lean_inc(v_val_2267_);
v___x_2327_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2267_);
v___x_2328_ = l_Lean_MessageData_ofExpr(v___x_2327_);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2326_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13);
v___x_2331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2244_, v___x_2331_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_dec_ref(v___x_2332_);
v___y_2315_ = v___y_2252_;
v___y_2316_ = v___y_2253_;
v___y_2317_ = v___y_2254_;
v___y_2318_ = v___y_2255_;
goto v___jp_2314_;
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec_ref(v___f_2313_);
lean_dec(v_val_2267_);
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
v___jp_2314_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2319_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8);
v___x_2320_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2321_, 0, v_val_2267_);
lean_ctor_set(v___x_2321_, 1, v___x_2319_);
lean_ctor_set(v___x_2321_, 2, v___x_2320_);
v___x_2322_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v___f_2313_, v___x_2321_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
return v___x_2322_;
}
}
else
{
lean_dec_ref(v_P_2246_);
goto v___jp_2270_;
}
}
v___jp_2270_:
{
lean_object* v_inheritedTraceOptions_2271_; lean_object* v___x_2272_; 
v_inheritedTraceOptions_2271_ = lean_ctor_get(v___y_2254_, 13);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc(v___y_2251_);
lean_inc_ref(v___y_2250_);
lean_inc(v___y_2249_);
lean_inc_ref(v_inheritedTraceOptions_2271_);
v___x_2272_ = lean_apply_9(v___f_2243_, v_inheritedTraceOptions_2271_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, lean_box(0));
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; uint8_t v___x_2274_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref(v___x_2272_);
v___x_2274_ = lean_unbox(v_a_2273_);
lean_dec(v_a_2273_);
if (v___x_2274_ == 0)
{
lean_dec(v_val_2269_);
lean_dec(v_val_2267_);
lean_dec(v_cls_2244_);
lean_dec_ref(v_rhs_2242_);
lean_dec_ref(v_lhs_2241_);
goto v___jp_2257_;
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2275_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2);
v___x_2276_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2267_);
v___x_2277_ = l_Lean_MessageData_ofExpr(v___x_2276_);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2275_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4);
v___x_2280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = l_Lean_indentExpr(v_lhs_2241_);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2269_);
v___x_2286_ = l_Lean_MessageData_ofExpr(v___x_2285_);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2284_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v___x_2279_);
v___x_2289_ = l_Lean_indentExpr(v_rhs_2242_);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2244_, v___x_2290_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_dec_ref(v___x_2291_);
goto v___jp_2257_;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec(v_val_2269_);
lean_dec(v_val_2267_);
lean_dec(v_cls_2244_);
lean_dec_ref(v_rhs_2242_);
lean_dec_ref(v_lhs_2241_);
v_a_2300_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2272_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2272_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2341_; lean_object* v___x_2342_; 
lean_dec(v___x_2268_);
lean_dec(v_val_2267_);
lean_dec_ref(v_P_2246_);
lean_dec_ref(v_lhs_2241_);
v_inheritedTraceOptions_2341_ = lean_ctor_get(v___y_2254_, 13);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc(v___y_2251_);
lean_inc_ref(v___y_2250_);
lean_inc(v___y_2249_);
lean_inc_ref(v_inheritedTraceOptions_2341_);
v___x_2342_ = lean_apply_9(v___f_2243_, v_inheritedTraceOptions_2341_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, lean_box(0));
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; uint8_t v___x_2344_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = lean_unbox(v_a_2343_);
lean_dec(v_a_2343_);
if (v___x_2344_ == 0)
{
lean_dec(v_cls_2244_);
lean_dec_ref(v_rhs_2242_);
goto v___jp_2260_;
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2345_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2346_ = l_Lean_indentExpr(v_rhs_2242_);
v___x_2347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2244_, v___x_2347_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_dec_ref(v___x_2348_);
goto v___jp_2260_;
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_cls_2244_);
lean_dec_ref(v_rhs_2242_);
v_a_2357_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2342_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2342_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2365_; lean_object* v___x_2366_; 
lean_dec(v___x_2266_);
lean_dec_ref(v_P_2246_);
lean_dec_ref(v_rhs_2242_);
v_inheritedTraceOptions_2365_ = lean_ctor_get(v___y_2254_, 13);
lean_inc(v___y_2255_);
lean_inc_ref(v___y_2254_);
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc(v___y_2251_);
lean_inc_ref(v___y_2250_);
lean_inc(v___y_2249_);
lean_inc_ref(v_inheritedTraceOptions_2365_);
v___x_2366_ = lean_apply_9(v___f_2243_, v_inheritedTraceOptions_2365_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, lean_box(0));
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; uint8_t v___x_2368_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref(v___x_2366_);
v___x_2368_ = lean_unbox(v_a_2367_);
lean_dec(v_a_2367_);
if (v___x_2368_ == 0)
{
lean_dec(v_cls_2244_);
lean_dec_ref(v_lhs_2241_);
goto v___jp_2263_;
}
else
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2369_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2370_ = l_Lean_indentExpr(v_lhs_2241_);
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2244_, v___x_2371_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_dec_ref(v___x_2372_);
goto v___jp_2263_;
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
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
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v_cls_2244_);
lean_dec_ref(v_lhs_2241_);
v_a_2381_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2366_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2366_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
v___jp_2257_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
return v___x_2259_;
}
v___jp_2260_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
v___jp_2263_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object* v_lhs_2389_, lean_object* v_rhs_2390_, lean_object* v___f_2391_, lean_object* v_cls_2392_, lean_object* v___x_2393_, lean_object* v_P_2394_, lean_object* v_hasTrace_2395_, lean_object* v_____r_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
uint8_t v___x_118788__boxed_2405_; uint8_t v_hasTrace_boxed_2406_; lean_object* v_res_2407_; 
v___x_118788__boxed_2405_ = lean_unbox(v___x_2393_);
v_hasTrace_boxed_2406_ = lean_unbox(v_hasTrace_2395_);
v_res_2407_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2389_, v_rhs_2390_, v___f_2391_, v_cls_2392_, v___x_118788__boxed_2405_, v_P_2394_, v_hasTrace_boxed_2406_, v_____r_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(lean_object* v_lhs_2408_, lean_object* v_rhs_2409_, lean_object* v_P_2410_, uint8_t v___x_2411_, lean_object* v_cls_2412_, lean_object* v___f_2413_, lean_object* v_____r_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___x_2432_; 
lean_inc_ref(v_lhs_2408_);
v___x_2432_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_lhs_2408_);
if (lean_obj_tag(v___x_2432_) == 1)
{
lean_object* v_val_2433_; lean_object* v___x_2434_; 
v_val_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_val_2433_);
lean_dec_ref(v___x_2432_);
lean_inc_ref(v_rhs_2409_);
v___x_2434_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_rhs_2409_);
if (lean_obj_tag(v___x_2434_) == 1)
{
lean_object* v_val_2435_; lean_object* v___x_2436_; lean_object* v___f_2437_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; uint8_t v___x_2469_; 
v_val_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_val_2435_);
lean_dec_ref(v___x_2434_);
v___x_2436_ = lean_box(v___x_2411_);
lean_inc_ref(v_rhs_2409_);
lean_inc_ref(v_lhs_2408_);
lean_inc(v_val_2433_);
v___f_2437_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed), 11, 5);
lean_closure_set(v___f_2437_, 0, v_val_2433_);
lean_closure_set(v___f_2437_, 1, v_lhs_2408_);
lean_closure_set(v___f_2437_, 2, v_rhs_2409_);
lean_closure_set(v___f_2437_, 3, v_P_2410_);
lean_closure_set(v___f_2437_, 4, v___x_2436_);
v___x_2469_ = lean_expr_eqv(v_val_2433_, v_val_2435_);
if (v___x_2469_ == 0)
{
if (v___x_2411_ == 0)
{
lean_dec(v_val_2435_);
lean_dec_ref(v___f_2413_);
lean_dec_ref(v_rhs_2409_);
lean_dec_ref(v_lhs_2408_);
goto v___jp_2447_;
}
else
{
lean_object* v_inheritedTraceOptions_2470_; lean_object* v___x_2471_; 
lean_dec_ref(v___f_2437_);
v_inheritedTraceOptions_2470_ = lean_ctor_get(v___y_2420_, 13);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
lean_inc(v___y_2415_);
lean_inc_ref(v_inheritedTraceOptions_2470_);
v___x_2471_ = lean_apply_9(v___f_2413_, v_inheritedTraceOptions_2470_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, lean_box(0));
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; uint8_t v___x_2473_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref(v___x_2471_);
v___x_2473_ = lean_unbox(v_a_2472_);
lean_dec(v_a_2472_);
if (v___x_2473_ == 0)
{
lean_dec(v_val_2435_);
lean_dec(v_val_2433_);
lean_dec(v_cls_2412_);
lean_dec_ref(v_rhs_2409_);
lean_dec_ref(v_lhs_2408_);
goto v___jp_2423_;
}
else
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2474_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2);
v___x_2475_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2433_);
v___x_2476_ = l_Lean_MessageData_ofExpr(v___x_2475_);
v___x_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2474_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4);
v___x_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = l_Lean_indentExpr(v_lhs_2408_);
v___x_2481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2435_);
v___x_2485_ = l_Lean_MessageData_ofExpr(v___x_2484_);
v___x_2486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2483_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v___x_2478_);
v___x_2488_ = l_Lean_indentExpr(v_rhs_2409_);
v___x_2489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2412_, v___x_2489_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_dec_ref(v___x_2490_);
goto v___jp_2423_;
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v_val_2435_);
lean_dec(v_val_2433_);
lean_dec(v_cls_2412_);
lean_dec_ref(v_rhs_2409_);
lean_dec_ref(v_lhs_2408_);
v_a_2499_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2471_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2471_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
else
{
lean_dec(v_val_2435_);
lean_dec_ref(v___f_2413_);
lean_dec_ref(v_rhs_2409_);
lean_dec_ref(v_lhs_2408_);
goto v___jp_2447_;
}
v___jp_2438_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2443_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8);
v___x_2444_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2445_, 0, v_val_2433_);
lean_ctor_set(v___x_2445_, 1, v___x_2443_);
lean_ctor_set(v___x_2445_, 2, v___x_2444_);
v___x_2446_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v___f_2437_, v___x_2445_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
return v___x_2446_;
}
v___jp_2447_:
{
lean_object* v_options_2448_; uint8_t v_hasTrace_2449_; 
v_options_2448_ = lean_ctor_get(v___y_2420_, 2);
v_hasTrace_2449_ = lean_ctor_get_uint8(v_options_2448_, sizeof(void*)*1);
if (v_hasTrace_2449_ == 0)
{
lean_dec(v_cls_2412_);
v___y_2439_ = v___y_2418_;
v___y_2440_ = v___y_2419_;
v___y_2441_ = v___y_2420_;
v___y_2442_ = v___y_2421_;
goto v___jp_2438_;
}
else
{
lean_object* v_inheritedTraceOptions_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v_inheritedTraceOptions_2450_ = lean_ctor_get(v___y_2420_, 13);
v___x_2451_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2412_);
v___x_2452_ = l_Lean_Name_append(v___x_2451_, v_cls_2412_);
v___x_2453_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2450_, v_options_2448_, v___x_2452_);
lean_dec(v___x_2452_);
if (v___x_2453_ == 0)
{
lean_dec(v_cls_2412_);
v___y_2439_ = v___y_2418_;
v___y_2440_ = v___y_2419_;
v___y_2441_ = v___y_2420_;
v___y_2442_ = v___y_2421_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2454_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11);
lean_inc(v_val_2433_);
v___x_2455_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2433_);
v___x_2456_ = l_Lean_MessageData_ofExpr(v___x_2455_);
v___x_2457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2454_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2412_, v___x_2459_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_dec_ref(v___x_2460_);
v___y_2439_ = v___y_2418_;
v___y_2440_ = v___y_2419_;
v___y_2441_ = v___y_2420_;
v___y_2442_ = v___y_2421_;
goto v___jp_2438_;
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec_ref(v___f_2437_);
lean_dec(v_val_2433_);
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2507_; lean_object* v___x_2508_; 
lean_dec(v___x_2434_);
lean_dec(v_val_2433_);
lean_dec_ref(v_P_2410_);
lean_dec_ref(v_lhs_2408_);
v_inheritedTraceOptions_2507_ = lean_ctor_get(v___y_2420_, 13);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
lean_inc(v___y_2415_);
lean_inc_ref(v_inheritedTraceOptions_2507_);
v___x_2508_ = lean_apply_9(v___f_2413_, v_inheritedTraceOptions_2507_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, lean_box(0));
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; uint8_t v___x_2510_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref(v___x_2508_);
v___x_2510_ = lean_unbox(v_a_2509_);
lean_dec(v_a_2509_);
if (v___x_2510_ == 0)
{
lean_dec(v_cls_2412_);
lean_dec_ref(v_rhs_2409_);
goto v___jp_2426_;
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2511_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2512_ = l_Lean_indentExpr(v_rhs_2409_);
v___x_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2412_, v___x_2513_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_dec_ref(v___x_2514_);
goto v___jp_2426_;
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2514_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2514_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_cls_2412_);
lean_dec_ref(v_rhs_2409_);
v_a_2523_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2508_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2508_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2531_; lean_object* v___x_2532_; 
lean_dec(v___x_2432_);
lean_dec_ref(v_P_2410_);
lean_dec_ref(v_rhs_2409_);
v_inheritedTraceOptions_2531_ = lean_ctor_get(v___y_2420_, 13);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
lean_inc(v___y_2415_);
lean_inc_ref(v_inheritedTraceOptions_2531_);
v___x_2532_ = lean_apply_9(v___f_2413_, v_inheritedTraceOptions_2531_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, lean_box(0));
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; uint8_t v___x_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref(v___x_2532_);
v___x_2534_ = lean_unbox(v_a_2533_);
lean_dec(v_a_2533_);
if (v___x_2534_ == 0)
{
lean_dec(v_cls_2412_);
lean_dec_ref(v_lhs_2408_);
goto v___jp_2429_;
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2535_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2536_ = l_Lean_indentExpr(v_lhs_2408_);
v___x_2537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2412_, v___x_2537_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_dec_ref(v___x_2538_);
goto v___jp_2429_;
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v_cls_2412_);
lean_dec_ref(v_lhs_2408_);
v_a_2547_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2532_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2532_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
v___jp_2423_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
v___jp_2426_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
return v___x_2428_;
}
v___jp_2429_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
return v___x_2431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8___boxed(lean_object* v_lhs_2555_, lean_object* v_rhs_2556_, lean_object* v_P_2557_, lean_object* v___x_2558_, lean_object* v_cls_2559_, lean_object* v___f_2560_, lean_object* v_____r_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
uint8_t v___x_119144__boxed_2570_; lean_object* v_res_2571_; 
v___x_119144__boxed_2570_ = lean_unbox(v___x_2558_);
v_res_2571_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(v_lhs_2555_, v_rhs_2556_, v_P_2557_, v___x_119144__boxed_2570_, v_cls_2559_, v___f_2560_, v_____r_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(lean_object* v_x_2572_){
_start:
{
if (lean_obj_tag(v_x_2572_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
v_a_2574_ = lean_ctor_get(v_x_2572_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_x_2572_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v_x_2572_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v_x_2572_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set_tag(v___x_2576_, 1);
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v_a_2582_ = lean_ctor_get(v_x_2572_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_x_2572_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v_x_2572_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v_x_2572_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 0);
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg___boxed(lean_object* v_x_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(v_x_2590_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5(size_t v_sz_2593_, size_t v_i_2594_, lean_object* v_bs_2595_){
_start:
{
uint8_t v___x_2596_; 
v___x_2596_ = lean_usize_dec_lt(v_i_2594_, v_sz_2593_);
if (v___x_2596_ == 0)
{
return v_bs_2595_;
}
else
{
lean_object* v_v_2597_; lean_object* v_msg_2598_; lean_object* v___x_2599_; lean_object* v_bs_x27_2600_; size_t v___x_2601_; size_t v___x_2602_; lean_object* v___x_2603_; 
v_v_2597_ = lean_array_uget_borrowed(v_bs_2595_, v_i_2594_);
v_msg_2598_ = lean_ctor_get(v_v_2597_, 1);
lean_inc_ref(v_msg_2598_);
v___x_2599_ = lean_unsigned_to_nat(0u);
v_bs_x27_2600_ = lean_array_uset(v_bs_2595_, v_i_2594_, v___x_2599_);
v___x_2601_ = ((size_t)1ULL);
v___x_2602_ = lean_usize_add(v_i_2594_, v___x_2601_);
v___x_2603_ = lean_array_uset(v_bs_x27_2600_, v_i_2594_, v_msg_2598_);
v_i_2594_ = v___x_2602_;
v_bs_2595_ = v___x_2603_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_2605_, lean_object* v_i_2606_, lean_object* v_bs_2607_){
_start:
{
size_t v_sz_boxed_2608_; size_t v_i_boxed_2609_; lean_object* v_res_2610_; 
v_sz_boxed_2608_ = lean_unbox_usize(v_sz_2605_);
lean_dec(v_sz_2605_);
v_i_boxed_2609_ = lean_unbox_usize(v_i_2606_);
lean_dec(v_i_2606_);
v_res_2610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5(v_sz_boxed_2608_, v_i_boxed_2609_, v_bs_2607_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_oldTraces_2611_, lean_object* v_data_2612_, lean_object* v_ref_2613_, lean_object* v_msg_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_fileName_2620_; lean_object* v_fileMap_2621_; lean_object* v_options_2622_; lean_object* v_currRecDepth_2623_; lean_object* v_maxRecDepth_2624_; lean_object* v_ref_2625_; lean_object* v_currNamespace_2626_; lean_object* v_openDecls_2627_; lean_object* v_initHeartbeats_2628_; lean_object* v_maxHeartbeats_2629_; lean_object* v_quotContext_2630_; lean_object* v_currMacroScope_2631_; uint8_t v_diag_2632_; lean_object* v_cancelTk_x3f_2633_; uint8_t v_suppressElabErrors_2634_; lean_object* v_inheritedTraceOptions_2635_; lean_object* v___x_2636_; lean_object* v_traceState_2637_; lean_object* v_traces_2638_; lean_object* v_ref_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; size_t v_sz_2642_; size_t v___x_2643_; lean_object* v___x_2644_; lean_object* v_msg_2645_; lean_object* v___x_2646_; lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2684_; 
v_fileName_2620_ = lean_ctor_get(v___y_2617_, 0);
v_fileMap_2621_ = lean_ctor_get(v___y_2617_, 1);
v_options_2622_ = lean_ctor_get(v___y_2617_, 2);
v_currRecDepth_2623_ = lean_ctor_get(v___y_2617_, 3);
v_maxRecDepth_2624_ = lean_ctor_get(v___y_2617_, 4);
v_ref_2625_ = lean_ctor_get(v___y_2617_, 5);
v_currNamespace_2626_ = lean_ctor_get(v___y_2617_, 6);
v_openDecls_2627_ = lean_ctor_get(v___y_2617_, 7);
v_initHeartbeats_2628_ = lean_ctor_get(v___y_2617_, 8);
v_maxHeartbeats_2629_ = lean_ctor_get(v___y_2617_, 9);
v_quotContext_2630_ = lean_ctor_get(v___y_2617_, 10);
v_currMacroScope_2631_ = lean_ctor_get(v___y_2617_, 11);
v_diag_2632_ = lean_ctor_get_uint8(v___y_2617_, sizeof(void*)*14);
v_cancelTk_x3f_2633_ = lean_ctor_get(v___y_2617_, 12);
v_suppressElabErrors_2634_ = lean_ctor_get_uint8(v___y_2617_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2635_ = lean_ctor_get(v___y_2617_, 13);
v___x_2636_ = lean_st_ref_get(v___y_2618_);
v_traceState_2637_ = lean_ctor_get(v___x_2636_, 4);
lean_inc_ref(v_traceState_2637_);
lean_dec(v___x_2636_);
v_traces_2638_ = lean_ctor_get(v_traceState_2637_, 0);
lean_inc_ref(v_traces_2638_);
lean_dec_ref(v_traceState_2637_);
v_ref_2639_ = l_Lean_replaceRef(v_ref_2613_, v_ref_2625_);
lean_inc_ref(v_inheritedTraceOptions_2635_);
lean_inc(v_cancelTk_x3f_2633_);
lean_inc(v_currMacroScope_2631_);
lean_inc(v_quotContext_2630_);
lean_inc(v_maxHeartbeats_2629_);
lean_inc(v_initHeartbeats_2628_);
lean_inc(v_openDecls_2627_);
lean_inc(v_currNamespace_2626_);
lean_inc(v_maxRecDepth_2624_);
lean_inc(v_currRecDepth_2623_);
lean_inc_ref(v_options_2622_);
lean_inc_ref(v_fileMap_2621_);
lean_inc_ref(v_fileName_2620_);
v___x_2640_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2640_, 0, v_fileName_2620_);
lean_ctor_set(v___x_2640_, 1, v_fileMap_2621_);
lean_ctor_set(v___x_2640_, 2, v_options_2622_);
lean_ctor_set(v___x_2640_, 3, v_currRecDepth_2623_);
lean_ctor_set(v___x_2640_, 4, v_maxRecDepth_2624_);
lean_ctor_set(v___x_2640_, 5, v_ref_2639_);
lean_ctor_set(v___x_2640_, 6, v_currNamespace_2626_);
lean_ctor_set(v___x_2640_, 7, v_openDecls_2627_);
lean_ctor_set(v___x_2640_, 8, v_initHeartbeats_2628_);
lean_ctor_set(v___x_2640_, 9, v_maxHeartbeats_2629_);
lean_ctor_set(v___x_2640_, 10, v_quotContext_2630_);
lean_ctor_set(v___x_2640_, 11, v_currMacroScope_2631_);
lean_ctor_set(v___x_2640_, 12, v_cancelTk_x3f_2633_);
lean_ctor_set(v___x_2640_, 13, v_inheritedTraceOptions_2635_);
lean_ctor_set_uint8(v___x_2640_, sizeof(void*)*14, v_diag_2632_);
lean_ctor_set_uint8(v___x_2640_, sizeof(void*)*14 + 1, v_suppressElabErrors_2634_);
v___x_2641_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2638_);
lean_dec_ref(v_traces_2638_);
v_sz_2642_ = lean_array_size(v___x_2641_);
v___x_2643_ = ((size_t)0ULL);
v___x_2644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4_spec__5(v_sz_2642_, v___x_2643_, v___x_2641_);
v_msg_2645_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2645_, 0, v_data_2612_);
lean_ctor_set(v_msg_2645_, 1, v_msg_2614_);
lean_ctor_set(v_msg_2645_, 2, v___x_2644_);
v___x_2646_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2645_, v___y_2615_, v___y_2616_, v___x_2640_, v___y_2618_);
lean_dec_ref(v___x_2640_);
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2649_ = v___x_2646_;
v_isShared_2650_ = v_isSharedCheck_2684_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2646_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2684_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2651_; lean_object* v_traceState_2652_; lean_object* v_env_2653_; lean_object* v_nextMacroScope_2654_; lean_object* v_ngen_2655_; lean_object* v_auxDeclNGen_2656_; lean_object* v_cache_2657_; lean_object* v_messages_2658_; lean_object* v_infoState_2659_; lean_object* v_snapshotTasks_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2683_; 
v___x_2651_ = lean_st_ref_take(v___y_2618_);
v_traceState_2652_ = lean_ctor_get(v___x_2651_, 4);
v_env_2653_ = lean_ctor_get(v___x_2651_, 0);
v_nextMacroScope_2654_ = lean_ctor_get(v___x_2651_, 1);
v_ngen_2655_ = lean_ctor_get(v___x_2651_, 2);
v_auxDeclNGen_2656_ = lean_ctor_get(v___x_2651_, 3);
v_cache_2657_ = lean_ctor_get(v___x_2651_, 5);
v_messages_2658_ = lean_ctor_get(v___x_2651_, 6);
v_infoState_2659_ = lean_ctor_get(v___x_2651_, 7);
v_snapshotTasks_2660_ = lean_ctor_get(v___x_2651_, 8);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2662_ = v___x_2651_;
v_isShared_2663_ = v_isSharedCheck_2683_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_snapshotTasks_2660_);
lean_inc(v_infoState_2659_);
lean_inc(v_messages_2658_);
lean_inc(v_cache_2657_);
lean_inc(v_traceState_2652_);
lean_inc(v_auxDeclNGen_2656_);
lean_inc(v_ngen_2655_);
lean_inc(v_nextMacroScope_2654_);
lean_inc(v_env_2653_);
lean_dec(v___x_2651_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2683_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
uint64_t v_tid_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2681_; 
v_tid_2664_ = lean_ctor_get_uint64(v_traceState_2652_, sizeof(void*)*1);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_traceState_2652_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; 
v_unused_2682_ = lean_ctor_get(v_traceState_2652_, 0);
lean_dec(v_unused_2682_);
v___x_2666_ = v_traceState_2652_;
v_isShared_2667_ = v_isSharedCheck_2681_;
goto v_resetjp_2665_;
}
else
{
lean_dec(v_traceState_2652_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2681_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
v___x_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2668_, 0, v_ref_2613_);
lean_ctor_set(v___x_2668_, 1, v_a_2647_);
v___x_2669_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2611_, v___x_2668_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2669_);
v___x_2671_ = v___x_2666_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2669_);
lean_ctor_set_uint64(v_reuseFailAlloc_2680_, sizeof(void*)*1, v_tid_2664_);
v___x_2671_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2673_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 4, v___x_2671_);
v___x_2673_ = v___x_2662_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_env_2653_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_nextMacroScope_2654_);
lean_ctor_set(v_reuseFailAlloc_2679_, 2, v_ngen_2655_);
lean_ctor_set(v_reuseFailAlloc_2679_, 3, v_auxDeclNGen_2656_);
lean_ctor_set(v_reuseFailAlloc_2679_, 4, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2679_, 5, v_cache_2657_);
lean_ctor_set(v_reuseFailAlloc_2679_, 6, v_messages_2658_);
lean_ctor_set(v_reuseFailAlloc_2679_, 7, v_infoState_2659_);
lean_ctor_set(v_reuseFailAlloc_2679_, 8, v_snapshotTasks_2660_);
v___x_2673_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2674_ = lean_st_ref_set(v___y_2618_, v___x_2673_);
v___x_2675_ = lean_box(0);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2675_);
v___x_2677_ = v___x_2649_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_oldTraces_2685_, lean_object* v_data_2686_, lean_object* v_ref_2687_, lean_object* v_msg_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_oldTraces_2685_, v_data_2686_, v_ref_2687_, v_msg_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2695_, lean_object* v_opt_2696_){
_start:
{
lean_object* v_name_2697_; lean_object* v_defValue_2698_; lean_object* v_map_2699_; lean_object* v___x_2700_; 
v_name_2697_ = lean_ctor_get(v_opt_2696_, 0);
v_defValue_2698_ = lean_ctor_get(v_opt_2696_, 1);
v_map_2699_ = lean_ctor_get(v_opts_2695_, 0);
v___x_2700_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2699_, v_name_2697_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_inc(v_defValue_2698_);
return v_defValue_2698_;
}
else
{
lean_object* v_val_2701_; 
v_val_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_val_2701_);
lean_dec_ref(v___x_2700_);
if (lean_obj_tag(v_val_2701_) == 3)
{
lean_object* v_v_2702_; 
v_v_2702_ = lean_ctor_get(v_val_2701_, 0);
lean_inc(v_v_2702_);
lean_dec_ref(v_val_2701_);
return v_v_2702_;
}
else
{
lean_dec(v_val_2701_);
lean_inc(v_defValue_2698_);
return v_defValue_2698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2703_, lean_object* v_opt_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2703_, v_opt_2704_);
lean_dec_ref(v_opt_2704_);
lean_dec_ref(v_opts_2703_);
return v_res_2705_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_e_2706_){
_start:
{
if (lean_obj_tag(v_e_2706_) == 0)
{
uint8_t v___x_2707_; 
v___x_2707_ = 2;
return v___x_2707_;
}
else
{
uint8_t v___x_2708_; 
v___x_2708_ = 0;
return v___x_2708_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_e_2709_){
_start:
{
uint8_t v_res_2710_; lean_object* v_r_2711_; 
v_res_2710_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_e_2709_);
lean_dec_ref(v_e_2709_);
v_r_2711_ = lean_box(v_res_2710_);
return v_r_2711_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_2714_ = l_Lean_stringToMessageData(v___x_2713_);
return v___x_2714_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2715_; double v___x_2716_; 
v___x_2715_ = lean_unsigned_to_nat(1000u);
v___x_2716_ = lean_float_of_nat(v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_2717_, uint8_t v_collapsed_2718_, lean_object* v_tag_2719_, lean_object* v_opts_2720_, uint8_t v_clsEnabled_2721_, lean_object* v_oldTraces_2722_, lean_object* v_msg_2723_, lean_object* v_resStartStop_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_fst_2733_; lean_object* v_snd_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2832_; 
v_fst_2733_ = lean_ctor_get(v_resStartStop_2724_, 0);
v_snd_2734_ = lean_ctor_get(v_resStartStop_2724_, 1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_resStartStop_2724_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2736_ = v_resStartStop_2724_;
v_isShared_2737_ = v_isSharedCheck_2832_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_snd_2734_);
lean_inc(v_fst_2733_);
lean_dec(v_resStartStop_2724_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2832_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v_data_2741_; lean_object* v_fst_2752_; lean_object* v_snd_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2831_; 
v_fst_2752_ = lean_ctor_get(v_snd_2734_, 0);
v_snd_2753_ = lean_ctor_get(v_snd_2734_, 1);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_snd_2734_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2755_ = v_snd_2734_;
v_isShared_2756_ = v_isSharedCheck_2831_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_snd_2753_);
lean_inc(v_fst_2752_);
lean_dec(v_snd_2734_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2831_;
goto v_resetjp_2754_;
}
v___jp_2738_:
{
lean_object* v___x_2742_; 
lean_inc(v___y_2739_);
v___x_2742_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_oldTraces_2722_, v_data_2741_, v___y_2739_, v___y_2740_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v___x_2743_; 
lean_dec_ref(v___x_2742_);
v___x_2743_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(v_fst_2733_);
return v___x_2743_;
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec(v_fst_2733_);
v_a_2744_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2742_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2742_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
v_resetjp_2754_:
{
lean_object* v___x_2757_; uint8_t v___x_2758_; lean_object* v___y_2760_; lean_object* v_a_2761_; uint8_t v___y_2785_; double v___y_2816_; 
v___x_2757_ = l_Lean_trace_profiler;
v___x_2758_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_opts_2720_, v___x_2757_);
if (v___x_2758_ == 0)
{
v___y_2785_ = v___x_2758_;
goto v___jp_2784_;
}
else
{
lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2821_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2822_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_opts_2720_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2824_; double v___x_2825_; double v___x_2826_; double v___x_2827_; 
v___x_2823_ = l_Lean_trace_profiler_threshold;
v___x_2824_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2720_, v___x_2823_);
v___x_2825_ = lean_float_of_nat(v___x_2824_);
v___x_2826_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_2827_ = lean_float_div(v___x_2825_, v___x_2826_);
v___y_2816_ = v___x_2827_;
goto v___jp_2815_;
}
else
{
lean_object* v___x_2828_; lean_object* v___x_2829_; double v___x_2830_; 
v___x_2828_ = l_Lean_trace_profiler_threshold;
v___x_2829_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2720_, v___x_2828_);
v___x_2830_ = lean_float_of_nat(v___x_2829_);
v___y_2816_ = v___x_2830_;
goto v___jp_2815_;
}
}
v___jp_2759_:
{
uint8_t v_result_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v_result_2762_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_fst_2733_);
v___x_2763_ = l_Lean_TraceResult_toEmoji(v_result_2762_);
v___x_2764_ = l_Lean_stringToMessageData(v___x_2763_);
v___x_2765_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10);
if (v_isShared_2756_ == 0)
{
lean_ctor_set_tag(v___x_2755_, 7);
lean_ctor_set(v___x_2755_, 1, v___x_2765_);
lean_ctor_set(v___x_2755_, 0, v___x_2764_);
v___x_2767_ = v___x_2755_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v_m_2769_; 
if (v_isShared_2737_ == 0)
{
lean_ctor_set_tag(v___x_2736_, 7);
lean_ctor_set(v___x_2736_, 1, v_a_2761_);
lean_ctor_set(v___x_2736_, 0, v___x_2767_);
v_m_2769_ = v___x_2736_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2767_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_a_2761_);
v_m_2769_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; double v___x_2772_; lean_object* v_data_2773_; 
v___x_2770_ = lean_box(v_result_2762_);
v___x_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
v___x_2772_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
lean_inc_ref(v_tag_2719_);
lean_inc_ref(v___x_2771_);
lean_inc(v_cls_2717_);
v_data_2773_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2773_, 0, v_cls_2717_);
lean_ctor_set(v_data_2773_, 1, v___x_2771_);
lean_ctor_set(v_data_2773_, 2, v_tag_2719_);
lean_ctor_set_float(v_data_2773_, sizeof(void*)*3, v___x_2772_);
lean_ctor_set_float(v_data_2773_, sizeof(void*)*3 + 8, v___x_2772_);
lean_ctor_set_uint8(v_data_2773_, sizeof(void*)*3 + 16, v_collapsed_2718_);
if (v___x_2758_ == 0)
{
lean_dec_ref(v___x_2771_);
lean_dec(v_snd_2753_);
lean_dec(v_fst_2752_);
lean_dec_ref(v_tag_2719_);
lean_dec(v_cls_2717_);
v___y_2739_ = v___y_2760_;
v___y_2740_ = v_m_2769_;
v_data_2741_ = v_data_2773_;
goto v___jp_2738_;
}
else
{
lean_object* v_data_2774_; double v___x_2775_; double v___x_2776_; 
lean_dec_ref(v_data_2773_);
v_data_2774_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2774_, 0, v_cls_2717_);
lean_ctor_set(v_data_2774_, 1, v___x_2771_);
lean_ctor_set(v_data_2774_, 2, v_tag_2719_);
v___x_2775_ = lean_unbox_float(v_fst_2752_);
lean_dec(v_fst_2752_);
lean_ctor_set_float(v_data_2774_, sizeof(void*)*3, v___x_2775_);
v___x_2776_ = lean_unbox_float(v_snd_2753_);
lean_dec(v_snd_2753_);
lean_ctor_set_float(v_data_2774_, sizeof(void*)*3 + 8, v___x_2776_);
lean_ctor_set_uint8(v_data_2774_, sizeof(void*)*3 + 16, v_collapsed_2718_);
v___y_2739_ = v___y_2760_;
v___y_2740_ = v_m_2769_;
v_data_2741_ = v_data_2774_;
goto v___jp_2738_;
}
}
}
}
v___jp_2779_:
{
lean_object* v_ref_2780_; lean_object* v___x_2781_; 
v_ref_2780_ = lean_ctor_get(v___y_2730_, 5);
lean_inc(v___y_2731_);
lean_inc_ref(v___y_2730_);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc(v_fst_2733_);
v___x_2781_ = lean_apply_9(v_msg_2723_, v_fst_2733_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, lean_box(0));
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref(v___x_2781_);
v___y_2760_ = v_ref_2780_;
v_a_2761_ = v_a_2782_;
goto v___jp_2759_;
}
else
{
lean_object* v___x_2783_; 
lean_dec_ref(v___x_2781_);
v___x_2783_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_2760_ = v_ref_2780_;
v_a_2761_ = v___x_2783_;
goto v___jp_2759_;
}
}
v___jp_2784_:
{
if (v_clsEnabled_2721_ == 0)
{
if (v___y_2785_ == 0)
{
lean_object* v___x_2786_; lean_object* v_traceState_2787_; lean_object* v_env_2788_; lean_object* v_nextMacroScope_2789_; lean_object* v_ngen_2790_; lean_object* v_auxDeclNGen_2791_; lean_object* v_cache_2792_; lean_object* v_messages_2793_; lean_object* v_infoState_2794_; lean_object* v_snapshotTasks_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2814_; 
lean_del_object(v___x_2755_);
lean_dec(v_snd_2753_);
lean_dec(v_fst_2752_);
lean_del_object(v___x_2736_);
lean_dec_ref(v_msg_2723_);
lean_dec_ref(v_tag_2719_);
lean_dec(v_cls_2717_);
v___x_2786_ = lean_st_ref_take(v___y_2731_);
v_traceState_2787_ = lean_ctor_get(v___x_2786_, 4);
v_env_2788_ = lean_ctor_get(v___x_2786_, 0);
v_nextMacroScope_2789_ = lean_ctor_get(v___x_2786_, 1);
v_ngen_2790_ = lean_ctor_get(v___x_2786_, 2);
v_auxDeclNGen_2791_ = lean_ctor_get(v___x_2786_, 3);
v_cache_2792_ = lean_ctor_get(v___x_2786_, 5);
v_messages_2793_ = lean_ctor_get(v___x_2786_, 6);
v_infoState_2794_ = lean_ctor_get(v___x_2786_, 7);
v_snapshotTasks_2795_ = lean_ctor_get(v___x_2786_, 8);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2797_ = v___x_2786_;
v_isShared_2798_ = v_isSharedCheck_2814_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_snapshotTasks_2795_);
lean_inc(v_infoState_2794_);
lean_inc(v_messages_2793_);
lean_inc(v_cache_2792_);
lean_inc(v_traceState_2787_);
lean_inc(v_auxDeclNGen_2791_);
lean_inc(v_ngen_2790_);
lean_inc(v_nextMacroScope_2789_);
lean_inc(v_env_2788_);
lean_dec(v___x_2786_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2814_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
uint64_t v_tid_2799_; lean_object* v_traces_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2813_; 
v_tid_2799_ = lean_ctor_get_uint64(v_traceState_2787_, sizeof(void*)*1);
v_traces_2800_ = lean_ctor_get(v_traceState_2787_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_traceState_2787_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2802_ = v_traceState_2787_;
v_isShared_2803_ = v_isSharedCheck_2813_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_traces_2800_);
lean_dec(v_traceState_2787_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2813_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2804_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2722_, v_traces_2800_);
lean_dec_ref(v_traces_2800_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2804_);
v___x_2806_ = v___x_2802_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2804_);
lean_ctor_set_uint64(v_reuseFailAlloc_2812_, sizeof(void*)*1, v_tid_2799_);
v___x_2806_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2808_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 4, v___x_2806_);
v___x_2808_ = v___x_2797_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_env_2788_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_nextMacroScope_2789_);
lean_ctor_set(v_reuseFailAlloc_2811_, 2, v_ngen_2790_);
lean_ctor_set(v_reuseFailAlloc_2811_, 3, v_auxDeclNGen_2791_);
lean_ctor_set(v_reuseFailAlloc_2811_, 4, v___x_2806_);
lean_ctor_set(v_reuseFailAlloc_2811_, 5, v_cache_2792_);
lean_ctor_set(v_reuseFailAlloc_2811_, 6, v_messages_2793_);
lean_ctor_set(v_reuseFailAlloc_2811_, 7, v_infoState_2794_);
lean_ctor_set(v_reuseFailAlloc_2811_, 8, v_snapshotTasks_2795_);
v___x_2808_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_st_ref_set(v___y_2731_, v___x_2808_);
v___x_2810_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(v_fst_2733_);
return v___x_2810_;
}
}
}
}
}
else
{
goto v___jp_2779_;
}
}
else
{
goto v___jp_2779_;
}
}
v___jp_2815_:
{
double v___x_2817_; double v___x_2818_; double v___x_2819_; uint8_t v___x_2820_; 
v___x_2817_ = lean_unbox_float(v_snd_2753_);
v___x_2818_ = lean_unbox_float(v_fst_2752_);
v___x_2819_ = lean_float_sub(v___x_2817_, v___x_2818_);
v___x_2820_ = lean_float_decLt(v___y_2816_, v___x_2819_);
v___y_2785_ = v___x_2820_;
goto v___jp_2784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object* v_cls_2833_, lean_object* v_collapsed_2834_, lean_object* v_tag_2835_, lean_object* v_opts_2836_, lean_object* v_clsEnabled_2837_, lean_object* v_oldTraces_2838_, lean_object* v_msg_2839_, lean_object* v_resStartStop_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
uint8_t v_collapsed_boxed_2849_; uint8_t v_clsEnabled_boxed_2850_; lean_object* v_res_2851_; 
v_collapsed_boxed_2849_ = lean_unbox(v_collapsed_2834_);
v_clsEnabled_boxed_2850_ = lean_unbox(v_clsEnabled_2837_);
v_res_2851_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_cls_2833_, v_collapsed_boxed_2849_, v_tag_2835_, v_opts_2836_, v_clsEnabled_boxed_2850_, v_oldTraces_2838_, v_msg_2839_, v_resStartStop_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v_opts_2836_);
return v_res_2851_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2(void){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1));
v___x_2856_ = l_Lean_stringToMessageData(v___x_2855_);
return v___x_2856_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4(void){
_start:
{
lean_object* v___x_2858_; double v___x_2859_; 
v___x_2858_ = lean_unsigned_to_nat(1000000000u);
v___x_2859_ = lean_float_of_nat(v___x_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(lean_object* v_P_2860_, lean_object* v_lhs_2861_, lean_object* v_rhs_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v_options_2891_; lean_object* v_inheritedTraceOptions_2892_; uint8_t v_hasTrace_2893_; lean_object* v_cls_2894_; lean_object* v___f_2895_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; uint8_t v_____do__lift_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; 
v_options_2891_ = lean_ctor_get(v_a_2868_, 2);
v_inheritedTraceOptions_2892_ = lean_ctor_get(v_a_2868_, 13);
v_hasTrace_2893_ = lean_ctor_get_uint8(v_options_2891_, sizeof(void*)*1);
v_cls_2894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_2895_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0));
if (v_hasTrace_2893_ == 0)
{
lean_object* v___x_3014_; lean_object* v_a_3015_; uint8_t v___x_3016_; 
v___x_3014_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2894_, v_inheritedTraceOptions_2892_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = lean_unbox(v_a_3015_);
lean_dec(v_a_3015_);
v_____do__lift_2993_ = v___x_3016_;
v___y_2994_ = v_a_2863_;
v___y_2995_ = v_a_2864_;
v___y_2996_ = v_a_2865_;
v___y_2997_ = v_a_2866_;
v___y_2998_ = v_a_2867_;
v___y_2999_ = v_a_2868_;
v___y_3000_ = v_a_2869_;
goto v___jp_2992_;
}
else
{
lean_object* v___f_3017_; uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v_a_3025_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v_a_3037_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v_a_3055_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v_a_3070_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; 
v___f_3017_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3));
v___x_3018_ = 0;
v___x_3019_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_3020_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3021_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2892_, v_options_2891_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3118_; uint8_t v___x_3119_; 
v___x_3118_ = l_Lean_trace_profiler;
v___x_3119_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_options_2891_, v___x_3118_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; lean_object* v_a_3121_; uint8_t v___x_3122_; 
v___x_3120_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2894_, v_inheritedTraceOptions_2892_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref(v___x_3120_);
v___x_3122_ = lean_unbox(v_a_3121_);
lean_dec(v_a_3121_);
v_____do__lift_2993_ = v___x_3122_;
v___y_2994_ = v_a_2863_;
v___y_2995_ = v_a_2864_;
v___y_2996_ = v_a_2865_;
v___y_2997_ = v_a_2866_;
v___y_2998_ = v_a_2867_;
v___y_2999_ = v_a_2868_;
v___y_3000_ = v_a_2869_;
goto v___jp_2992_;
}
else
{
goto v___jp_3085_;
}
}
else
{
goto v___jp_3085_;
}
v___jp_3022_:
{
lean_object* v___x_3026_; double v___x_3027_; double v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3026_ = lean_io_get_num_heartbeats();
v___x_3027_ = lean_float_of_nat(v___y_3024_);
v___x_3028_ = lean_float_of_nat(v___x_3026_);
v___x_3029_ = lean_box_float(v___x_3027_);
v___x_3030_ = lean_box_float(v___x_3028_);
v___x_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v_a_3025_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_cls_2894_, v___x_3018_, v___x_3019_, v_options_2891_, v___x_3021_, v___y_3023_, v___f_3017_, v___x_3032_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
return v___x_3033_;
}
v___jp_3034_:
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v_a_3037_);
v___y_3023_ = v___y_3035_;
v___y_3024_ = v___y_3036_;
v_a_3025_ = v___x_3038_;
goto v___jp_3022_;
}
v___jp_3039_:
{
if (lean_obj_tag(v___y_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
v_a_3043_ = lean_ctor_get(v___y_3042_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___y_3042_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___y_3042_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___y_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set_tag(v___x_3045_, 1);
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
v___y_3023_ = v___y_3040_;
v___y_3024_ = v___y_3041_;
v_a_3025_ = v___x_3048_;
goto v___jp_3022_;
}
}
}
else
{
lean_object* v_a_3051_; 
v_a_3051_ = lean_ctor_get(v___y_3042_, 0);
lean_inc(v_a_3051_);
lean_dec_ref(v___y_3042_);
v___y_3035_ = v___y_3040_;
v___y_3036_ = v___y_3041_;
v_a_3037_ = v_a_3051_;
goto v___jp_3034_;
}
}
v___jp_3052_:
{
lean_object* v___x_3056_; double v___x_3057_; double v___x_3058_; double v___x_3059_; double v___x_3060_; double v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3056_ = lean_io_mono_nanos_now();
v___x_3057_ = lean_float_of_nat(v___y_3053_);
v___x_3058_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__4);
v___x_3059_ = lean_float_div(v___x_3057_, v___x_3058_);
v___x_3060_ = lean_float_of_nat(v___x_3056_);
v___x_3061_ = lean_float_div(v___x_3060_, v___x_3058_);
v___x_3062_ = lean_box_float(v___x_3059_);
v___x_3063_ = lean_box_float(v___x_3061_);
v___x_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3062_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_a_3055_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_cls_2894_, v___x_3018_, v___x_3019_, v_options_2891_, v___x_3021_, v___y_3054_, v___f_3017_, v___x_3065_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
return v___x_3066_;
}
v___jp_3067_:
{
lean_object* v___x_3071_; 
v___x_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3071_, 0, v_a_3070_);
v___y_3053_ = v___y_3068_;
v___y_3054_ = v___y_3069_;
v_a_3055_ = v___x_3071_;
goto v___jp_3052_;
}
v___jp_3072_:
{
if (lean_obj_tag(v___y_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
v_a_3076_ = lean_ctor_get(v___y_3075_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___y_3075_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___y_3075_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___y_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
lean_ctor_set_tag(v___x_3078_, 1);
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
v___y_3053_ = v___y_3073_;
v___y_3054_ = v___y_3074_;
v_a_3055_ = v___x_3081_;
goto v___jp_3052_;
}
}
}
else
{
lean_object* v_a_3084_; 
v_a_3084_ = lean_ctor_get(v___y_3075_, 0);
lean_inc(v_a_3084_);
lean_dec_ref(v___y_3075_);
v___y_3068_ = v___y_3073_;
v___y_3069_ = v___y_3074_;
v_a_3070_ = v_a_3084_;
goto v___jp_3067_;
}
}
v___jp_3085_:
{
lean_object* v___x_3086_; lean_object* v_a_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3086_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_2869_);
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref(v___x_3086_);
v___x_3088_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3089_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v_options_2891_, v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v_a_3092_; uint8_t v___x_3093_; 
v___x_3090_ = lean_io_mono_nanos_now();
v___x_3091_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2894_, v_inheritedTraceOptions_2892_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_a_3092_);
lean_dec_ref(v___x_3091_);
v___x_3093_ = lean_unbox(v_a_3092_);
lean_dec(v_a_3092_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = lean_box(0);
v___x_3095_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2861_, v_rhs_2862_, v___f_2895_, v_cls_2894_, v___x_3089_, v_P_2860_, v_hasTrace_2893_, v___x_3094_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
v___y_3073_ = v___x_3090_;
v___y_3074_ = v_a_3087_;
v___y_3075_ = v___x_3095_;
goto v___jp_3072_;
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3096_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2862_);
lean_inc_ref(v_lhs_2861_);
lean_inc_ref(v_P_2860_);
v___x_3097_ = l_Lean_mkAppB(v_P_2860_, v_lhs_2861_, v_rhs_2862_);
v___x_3098_ = l_Lean_indentExpr(v___x_3097_);
v___x_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3096_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2894_, v___x_3099_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3102_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref(v___x_3100_);
v___x_3102_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2861_, v_rhs_2862_, v___f_2895_, v_cls_2894_, v___x_3089_, v_P_2860_, v_hasTrace_2893_, v_a_3101_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
v___y_3073_ = v___x_3090_;
v___y_3074_ = v_a_3087_;
v___y_3075_ = v___x_3102_;
goto v___jp_3072_;
}
else
{
lean_object* v_a_3103_; 
lean_dec_ref(v_rhs_2862_);
lean_dec_ref(v_lhs_2861_);
lean_dec_ref(v_P_2860_);
v_a_3103_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3103_);
lean_dec_ref(v___x_3100_);
v___y_3068_ = v___x_3090_;
v___y_3069_ = v_a_3087_;
v_a_3070_ = v_a_3103_;
goto v___jp_3067_;
}
}
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v_a_3106_; uint8_t v___x_3107_; 
v___x_3104_ = lean_io_get_num_heartbeats();
v___x_3105_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2894_, v_inheritedTraceOptions_2892_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref(v___x_3105_);
v___x_3107_ = lean_unbox(v_a_3106_);
lean_dec(v_a_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = lean_box(0);
v___x_3109_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(v_lhs_2861_, v_rhs_2862_, v_P_2860_, v___x_3089_, v_cls_2894_, v___f_2895_, v___x_3108_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
v___y_3040_ = v_a_3087_;
v___y_3041_ = v___x_3104_;
v___y_3042_ = v___x_3109_;
goto v___jp_3039_;
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3110_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2862_);
lean_inc_ref(v_lhs_2861_);
lean_inc_ref(v_P_2860_);
v___x_3111_ = l_Lean_mkAppB(v_P_2860_, v_lhs_2861_, v_rhs_2862_);
v___x_3112_ = l_Lean_indentExpr(v___x_3111_);
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3110_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2894_, v___x_3113_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3116_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref(v___x_3114_);
v___x_3116_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__8(v_lhs_2861_, v_rhs_2862_, v_P_2860_, v___x_3089_, v_cls_2894_, v___f_2895_, v_a_3115_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
v___y_3040_ = v_a_3087_;
v___y_3041_ = v___x_3104_;
v___y_3042_ = v___x_3116_;
goto v___jp_3039_;
}
else
{
lean_object* v_a_3117_; 
lean_dec_ref(v_rhs_2862_);
lean_dec_ref(v_lhs_2861_);
lean_dec_ref(v_P_2860_);
v_a_3117_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3117_);
lean_dec_ref(v___x_3114_);
v___y_3035_ = v_a_3087_;
v___y_3036_ = v___x_3104_;
v_a_3037_ = v_a_3117_;
goto v___jp_3034_;
}
}
}
}
}
v___jp_2871_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
return v___x_2873_;
}
v___jp_2874_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
v___jp_2877_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
return v___x_2879_;
}
v___jp_2880_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2887_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__8);
v___x_2888_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2889_, 0, v___y_2882_);
lean_ctor_set(v___x_2889_, 1, v___x_2887_);
lean_ctor_set(v___x_2889_, 2, v___x_2888_);
v___x_2890_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v___y_2881_, v___x_2889_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
return v___x_2890_;
}
v___jp_2896_:
{
lean_object* v___x_2904_; 
lean_inc_ref(v_lhs_2861_);
v___x_2904_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_lhs_2861_);
if (lean_obj_tag(v___x_2904_) == 1)
{
lean_object* v_val_2905_; lean_object* v___x_2906_; 
v_val_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_val_2905_);
lean_dec_ref(v___x_2904_);
lean_inc_ref(v_rhs_2862_);
v___x_2906_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_rhs_2862_);
if (lean_obj_tag(v___x_2906_) == 1)
{
lean_object* v_val_2907_; uint8_t v___x_2908_; 
v_val_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_val_2907_);
lean_dec_ref(v___x_2906_);
v___x_2908_ = lean_expr_eqv(v_val_2905_, v_val_2907_);
if (v___x_2908_ == 0)
{
lean_object* v_inheritedTraceOptions_2909_; lean_object* v___x_2910_; lean_object* v_a_2911_; uint8_t v___x_2912_; 
lean_dec_ref(v_P_2860_);
v_inheritedTraceOptions_2909_ = lean_ctor_get(v___y_2902_, 13);
v___x_2910_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2894_, v_inheritedTraceOptions_2909_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref(v___x_2910_);
v___x_2912_ = lean_unbox(v_a_2911_);
lean_dec(v_a_2911_);
if (v___x_2912_ == 0)
{
lean_dec(v_val_2907_);
lean_dec(v_val_2905_);
lean_dec_ref(v_rhs_2862_);
lean_dec_ref(v_lhs_2861_);
goto v___jp_2877_;
}
else
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2913_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__2);
v___x_2914_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2905_);
v___x_2915_ = l_Lean_MessageData_ofExpr(v___x_2914_);
v___x_2916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2913_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__4);
v___x_2918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2916_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = l_Lean_indentExpr(v_lhs_2861_);
v___x_2920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2918_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2920_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___x_2923_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2907_);
v___x_2924_ = l_Lean_MessageData_ofExpr(v___x_2923_);
v___x_2925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2922_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
lean_ctor_set(v___x_2926_, 1, v___x_2917_);
v___x_2927_ = l_Lean_indentExpr(v_rhs_2862_);
v___x_2928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2894_, v___x_2928_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_dec_ref(v___x_2929_);
goto v___jp_2877_;
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2929_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
else
{
lean_object* v_options_2938_; lean_object* v_inheritedTraceOptions_2939_; uint8_t v_hasTrace_2940_; lean_object* v___x_2941_; lean_object* v___f_2942_; 
lean_dec(v_val_2907_);
v_options_2938_ = lean_ctor_get(v___y_2902_, 2);
v_inheritedTraceOptions_2939_ = lean_ctor_get(v___y_2902_, 13);
v_hasTrace_2940_ = lean_ctor_get_uint8(v_options_2938_, sizeof(void*)*1);
v___x_2941_ = lean_box(v___x_2908_);
lean_inc(v_val_2905_);
v___f_2942_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed), 11, 5);
lean_closure_set(v___f_2942_, 0, v_val_2905_);
lean_closure_set(v___f_2942_, 1, v_lhs_2861_);
lean_closure_set(v___f_2942_, 2, v_rhs_2862_);
lean_closure_set(v___f_2942_, 3, v_P_2860_);
lean_closure_set(v___f_2942_, 4, v___x_2941_);
if (v_hasTrace_2940_ == 0)
{
v___y_2881_ = v___f_2942_;
v___y_2882_ = v_val_2905_;
v___y_2883_ = v___y_2900_;
v___y_2884_ = v___y_2901_;
v___y_2885_ = v___y_2902_;
v___y_2886_ = v___y_2903_;
goto v___jp_2880_;
}
else
{
lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2943_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_2944_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2939_, v_options_2938_, v___x_2943_);
if (v___x_2944_ == 0)
{
v___y_2881_ = v___f_2942_;
v___y_2882_ = v_val_2905_;
v___y_2883_ = v___y_2900_;
v___y_2884_ = v___y_2901_;
v___y_2885_ = v___y_2902_;
v___y_2886_ = v___y_2903_;
goto v___jp_2880_;
}
else
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2945_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__11);
lean_inc(v_val_2905_);
v___x_2946_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2905_);
v___x_2947_ = l_Lean_MessageData_ofExpr(v___x_2946_);
v___x_2948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2945_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__13);
v___x_2950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2948_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2894_, v___x_2950_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_dec_ref(v___x_2951_);
v___y_2881_ = v___f_2942_;
v___y_2882_ = v_val_2905_;
v___y_2883_ = v___y_2900_;
v___y_2884_ = v___y_2901_;
v___y_2885_ = v___y_2902_;
v___y_2886_ = v___y_2903_;
goto v___jp_2880_;
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec_ref(v___f_2942_);
lean_dec(v_val_2905_);
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2951_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2960_; lean_object* v___x_2961_; lean_object* v_a_2962_; uint8_t v___x_2963_; 
lean_dec(v___x_2906_);
lean_dec(v_val_2905_);
lean_dec_ref(v_lhs_2861_);
lean_dec_ref(v_P_2860_);
v_inheritedTraceOptions_2960_ = lean_ctor_get(v___y_2902_, 13);
v___x_2961_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2894_, v_inheritedTraceOptions_2960_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref(v___x_2961_);
v___x_2963_ = lean_unbox(v_a_2962_);
lean_dec(v_a_2962_);
if (v___x_2963_ == 0)
{
lean_dec_ref(v_rhs_2862_);
goto v___jp_2874_;
}
else
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2964_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2965_ = l_Lean_indentExpr(v_rhs_2862_);
v___x_2966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2964_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2894_, v___x_2966_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_dec_ref(v___x_2967_);
goto v___jp_2874_;
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2976_; lean_object* v___x_2977_; lean_object* v_a_2978_; uint8_t v___x_2979_; 
lean_dec(v___x_2904_);
lean_dec_ref(v_rhs_2862_);
lean_dec_ref(v_P_2860_);
v_inheritedTraceOptions_2976_ = lean_ctor_get(v___y_2902_, 13);
v___x_2977_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(v_cls_2894_, v_inheritedTraceOptions_2976_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref(v___x_2977_);
v___x_2979_ = lean_unbox(v_a_2978_);
lean_dec(v_a_2978_);
if (v___x_2979_ == 0)
{
lean_dec_ref(v_lhs_2861_);
goto v___jp_2871_;
}
else
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2980_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2981_ = l_Lean_indentExpr(v_lhs_2861_);
v___x_2982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2894_, v___x_2982_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_dec_ref(v___x_2983_);
goto v___jp_2871_;
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
}
}
v___jp_2992_:
{
if (v_____do__lift_2993_ == 0)
{
v___y_2897_ = v___y_2994_;
v___y_2898_ = v___y_2995_;
v___y_2899_ = v___y_2996_;
v___y_2900_ = v___y_2997_;
v___y_2901_ = v___y_2998_;
v___y_2902_ = v___y_2999_;
v___y_2903_ = v___y_3000_;
goto v___jp_2896_;
}
else
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3001_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2862_);
lean_inc_ref(v_lhs_2861_);
lean_inc_ref(v_P_2860_);
v___x_3002_ = l_Lean_mkAppB(v_P_2860_, v_lhs_2861_, v_rhs_2862_);
v___x_3003_ = l_Lean_indentExpr(v___x_3002_);
v___x_3004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3001_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2894_, v___x_3004_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_dec_ref(v___x_3005_);
v___y_2897_ = v___y_2994_;
v___y_2898_ = v___y_2995_;
v___y_2899_ = v___y_2996_;
v___y_2900_ = v___y_2997_;
v___y_2901_ = v___y_2998_;
v___y_2902_ = v___y_2999_;
v___y_2903_ = v___y_3000_;
goto v___jp_2896_;
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_dec_ref(v_rhs_2862_);
lean_dec_ref(v_lhs_2861_);
lean_dec_ref(v_P_2860_);
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_3005_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3123_, lean_object* v_lhs_3124_, lean_object* v_rhs_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(v_P_3123_, v_lhs_3124_, v_rhs_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec(v_a_3130_);
lean_dec_ref(v_a_3129_);
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3135_, lean_object* v_msg_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3135_, v_msg_3136_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3146_, lean_object* v_msg_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0(v_cls_3146_, v_msg_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_00_u03b1_3157_, lean_object* v_x_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___redArg(v_x_3158_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3168_, lean_object* v_x_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_00_u03b1_3168_, v_x_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_oldTraces_3179_, lean_object* v_data_3180_, lean_object* v_ref_3181_, lean_object* v_msg_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_oldTraces_3179_, v_data_3180_, v_ref_3181_, v_msg_3182_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_oldTraces_3192_, lean_object* v_data_3193_, lean_object* v_ref_3194_, lean_object* v_msg_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_oldTraces_3192_, v_data_3193_, v_ref_3194_, v_msg_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
return v_res_3204_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__5));
v___x_3215_ = l_Lean_stringToMessageData(v___x_3214_);
return v___x_3215_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = l_Lean_checkEmoji;
v___x_3217_ = l_Lean_stringToMessageData(v___x_3216_);
return v___x_3217_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7);
v___x_3219_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6);
v___x_3220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
lean_ctor_set(v___x_3220_, 1, v___x_3218_);
return v___x_3220_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__9));
v___x_3223_ = l_Lean_stringToMessageData(v___x_3222_);
return v___x_3223_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10);
v___x_3225_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8);
v___x_3226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
lean_ctor_set(v___x_3226_, 1, v___x_3224_);
return v___x_3226_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13(void){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__12));
v___x_3229_ = l_Lean_stringToMessageData(v___x_3228_);
return v___x_3229_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13);
v___x_3231_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8);
v___x_3232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v___x_3230_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost(lean_object* v_e_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3233_, v_a_3238_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3349_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3349_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3349_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3252_; uint8_t v___x_3253_; 
v___x_3252_ = l_Lean_Expr_cleanupAnnotations(v_a_3243_);
v___x_3253_ = l_Lean_Expr_isApp(v___x_3252_);
if (v___x_3253_ == 0)
{
lean_dec_ref(v___x_3252_);
goto v___jp_3247_;
}
else
{
lean_object* v_arg_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v_arg_3254_ = lean_ctor_get(v___x_3252_, 1);
lean_inc_ref(v_arg_3254_);
v___x_3255_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3252_);
v___x_3256_ = l_Lean_Expr_isApp(v___x_3255_);
if (v___x_3256_ == 0)
{
lean_dec_ref(v___x_3255_);
lean_dec_ref(v_arg_3254_);
goto v___jp_3247_;
}
else
{
lean_object* v_arg_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v_arg_3257_ = lean_ctor_get(v___x_3255_, 1);
lean_inc_ref(v_arg_3257_);
v___x_3258_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3255_);
v___x_3259_ = l_Lean_Expr_isApp(v___x_3258_);
if (v___x_3259_ == 0)
{
lean_dec_ref(v___x_3258_);
lean_dec_ref(v_arg_3257_);
lean_dec_ref(v_arg_3254_);
goto v___jp_3247_;
}
else
{
lean_object* v_arg_3260_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v_arg_3260_ = lean_ctor_get(v___x_3258_, 1);
lean_inc_ref(v_arg_3260_);
v___x_3285_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3258_);
v___x_3286_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1));
v___x_3287_ = l_Lean_Expr_isConstOf(v___x_3285_, v___x_3286_);
if (v___x_3287_ == 0)
{
uint8_t v___x_3288_; 
v___x_3288_ = l_Lean_Expr_isApp(v___x_3285_);
if (v___x_3288_ == 0)
{
lean_dec_ref(v___x_3285_);
lean_dec_ref(v_arg_3260_);
lean_dec_ref(v_arg_3257_);
lean_dec_ref(v_arg_3254_);
goto v___jp_3247_;
}
else
{
lean_object* v_arg_3289_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___x_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v_arg_3289_ = lean_ctor_get(v___x_3285_, 1);
lean_inc_ref(v_arg_3289_);
v___x_3314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3285_);
v___x_3315_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4));
v___x_3316_ = l_Lean_Expr_isConstOf(v___x_3314_, v___x_3315_);
lean_dec_ref(v___x_3314_);
if (v___x_3316_ == 0)
{
lean_dec_ref(v_arg_3289_);
lean_dec_ref(v_arg_3260_);
lean_dec_ref(v_arg_3257_);
lean_dec_ref(v_arg_3254_);
goto v___jp_3247_;
}
else
{
lean_object* v_options_3317_; uint8_t v_hasTrace_3318_; 
lean_del_object(v___x_3245_);
v_options_3317_ = lean_ctor_get(v_a_3239_, 2);
v_hasTrace_3318_ = lean_ctor_get_uint8(v_options_3317_, sizeof(void*)*1);
if (v_hasTrace_3318_ == 0)
{
v___y_3291_ = v_a_3234_;
v___y_3292_ = v_a_3235_;
v___y_3293_ = v_a_3236_;
v___y_3294_ = v_a_3237_;
v___y_3295_ = v_a_3238_;
v___y_3296_ = v_a_3239_;
v___y_3297_ = v_a_3240_;
goto v___jp_3290_;
}
else
{
lean_object* v_inheritedTraceOptions_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v_inheritedTraceOptions_3319_ = lean_ctor_get(v_a_3239_, 13);
v___x_3320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3321_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3322_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3319_, v_options_3317_, v___x_3321_);
if (v___x_3322_ == 0)
{
v___y_3291_ = v_a_3234_;
v___y_3292_ = v_a_3235_;
v___y_3293_ = v_a_3236_;
v___y_3294_ = v_a_3237_;
v___y_3295_ = v_a_3238_;
v___y_3296_ = v_a_3239_;
v___y_3297_ = v_a_3240_;
goto v___jp_3290_;
}
else
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11);
v___x_3324_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3320_, v___x_3323_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_dec_ref(v___x_3324_);
v___y_3291_ = v_a_3234_;
v___y_3292_ = v_a_3235_;
v___y_3293_ = v_a_3236_;
v___y_3294_ = v_a_3237_;
v___y_3295_ = v_a_3238_;
v___y_3296_ = v_a_3239_;
v___y_3297_ = v_a_3240_;
goto v___jp_3290_;
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec_ref(v_arg_3289_);
lean_dec_ref(v_arg_3260_);
lean_dec_ref(v_arg_3257_);
lean_dec_ref(v_arg_3254_);
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3324_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3324_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
}
}
v___jp_3290_:
{
lean_object* v___x_3298_; 
lean_inc_ref(v_arg_3289_);
v___x_3298_ = l_Lean_Meta_getDecLevel(v_arg_3289_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref(v___x_3298_);
v___x_3300_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4));
v___x_3301_ = lean_box(0);
v___x_3302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3302_, 0, v_a_3299_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = l_Lean_Expr_const___override(v___x_3300_, v___x_3302_);
v___x_3304_ = l_Lean_mkAppB(v___x_3303_, v_arg_3289_, v_arg_3260_);
v___x_3305_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(v___x_3304_, v_arg_3257_, v_arg_3254_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3305_;
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec_ref(v_arg_3289_);
lean_dec_ref(v_arg_3260_);
lean_dec_ref(v_arg_3257_);
lean_dec_ref(v_arg_3254_);
v_a_3306_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3298_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3298_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
}
}
else
{
lean_object* v_options_3333_; uint8_t v_hasTrace_3334_; 
lean_dec_ref(v___x_3285_);
lean_del_object(v___x_3245_);
v_options_3333_ = lean_ctor_get(v_a_3239_, 2);
v_hasTrace_3334_ = lean_ctor_get_uint8(v_options_3333_, sizeof(void*)*1);
if (v_hasTrace_3334_ == 0)
{
v___y_3262_ = v_a_3234_;
v___y_3263_ = v_a_3235_;
v___y_3264_ = v_a_3236_;
v___y_3265_ = v_a_3237_;
v___y_3266_ = v_a_3238_;
v___y_3267_ = v_a_3239_;
v___y_3268_ = v_a_3240_;
goto v___jp_3261_;
}
else
{
lean_object* v_inheritedTraceOptions_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v_inheritedTraceOptions_3335_ = lean_ctor_get(v_a_3239_, 13);
v___x_3336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3337_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3338_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3335_, v_options_3333_, v___x_3337_);
if (v___x_3338_ == 0)
{
v___y_3262_ = v_a_3234_;
v___y_3263_ = v_a_3235_;
v___y_3264_ = v_a_3236_;
v___y_3265_ = v_a_3237_;
v___y_3266_ = v_a_3238_;
v___y_3267_ = v_a_3239_;
v___y_3268_ = v_a_3240_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14);
v___x_3340_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3336_, v___x_3339_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_dec_ref(v___x_3340_);
v___y_3262_ = v_a_3234_;
v___y_3263_ = v_a_3235_;
v___y_3264_ = v_a_3236_;
v___y_3265_ = v_a_3237_;
v___y_3266_ = v_a_3238_;
v___y_3267_ = v_a_3239_;
v___y_3268_ = v_a_3240_;
goto v___jp_3261_;
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec_ref(v_arg_3260_);
lean_dec_ref(v_arg_3257_);
lean_dec_ref(v_arg_3254_);
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3340_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3340_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
}
v___jp_3261_:
{
lean_object* v___x_3269_; 
lean_inc_ref(v_arg_3260_);
v___x_3269_ = l_Lean_Meta_getLevel(v_arg_3260_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___x_3269_);
v___x_3271_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1));
v___x_3272_ = lean_box(0);
v___x_3273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3273_, 0, v_a_3270_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = l_Lean_Expr_const___override(v___x_3271_, v___x_3273_);
v___x_3275_ = l_Lean_Expr_app___override(v___x_3274_, v_arg_3260_);
v___x_3276_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(v___x_3275_, v_arg_3257_, v_arg_3254_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
return v___x_3276_;
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec_ref(v_arg_3260_);
lean_dec_ref(v_arg_3257_);
lean_dec_ref(v_arg_3254_);
v_a_3277_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3269_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3269_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
}
}
v___jp_3247_:
{
lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3248_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3248_);
v___x_3250_ = v___x_3245_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
v_a_3350_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3242_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3242_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed(lean_object* v_e_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost(v_e_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_);
lean_dec(v_a_3365_);
lean_dec_ref(v_a_3364_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
lean_dec(v_a_3359_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0(lean_object* v_x_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0___boxed(lean_object* v_x_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0(v_x_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v_x_3379_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1(lean_object* v_x_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___closed__0));
v___x_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___boxed(lean_object* v_x_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1(v_x_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v_x_3402_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2(lean_object* v_e_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_e_3412_);
v___x_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2___boxed(lean_object* v_e_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2(v_e_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3(lean_object* v_x_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = lean_box(0);
v___x_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3___boxed(lean_object* v_x_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3(v_x_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v_x_3444_);
return v_res_3453_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5(void){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3460_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6(void){
_start:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3461_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5);
v___x_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
return v___x_3462_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7(void){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3463_ = lean_unsigned_to_nat(0u);
v___x_3464_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6);
v___x_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
lean_ctor_set(v___x_3465_, 1, v___x_3463_);
return v___x_3465_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8(void){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3466_ = lean_unsigned_to_nat(32u);
v___x_3467_ = lean_mk_empty_array_with_capacity(v___x_3466_);
v___x_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
return v___x_3468_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9(void){
_start:
{
size_t v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3469_ = ((size_t)5ULL);
v___x_3470_ = lean_unsigned_to_nat(0u);
v___x_3471_ = lean_unsigned_to_nat(32u);
v___x_3472_ = lean_mk_empty_array_with_capacity(v___x_3471_);
v___x_3473_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8);
v___x_3474_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___x_3472_);
lean_ctor_set(v___x_3474_, 2, v___x_3470_);
lean_ctor_set(v___x_3474_, 3, v___x_3470_);
lean_ctor_set_usize(v___x_3474_, 4, v___x_3469_);
return v___x_3474_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10(void){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9);
v___x_3476_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6);
v___x_3477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
lean_ctor_set(v___x_3477_, 2, v___x_3476_);
lean_ctor_set(v___x_3477_, 3, v___x_3475_);
return v___x_3477_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11(void){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10);
v___x_3479_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7);
v___x_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
lean_ctor_set(v___x_3480_, 1, v___x_3478_);
return v___x_3480_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12(void){
_start:
{
uint8_t v___x_3481_; lean_object* v___f_3482_; lean_object* v___f_3483_; lean_object* v___f_3484_; lean_object* v___x_3485_; lean_object* v___f_3486_; lean_object* v___x_3487_; 
v___x_3481_ = 1;
v___f_3482_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4));
v___f_3483_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3));
v___f_3484_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2));
v___x_3485_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed), 9, 0);
v___f_3486_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1));
v___x_3487_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3487_, 0, v___f_3486_);
lean_ctor_set(v___x_3487_, 1, v___x_3485_);
lean_ctor_set(v___x_3487_, 2, v___f_3484_);
lean_ctor_set(v___x_3487_, 3, v___f_3483_);
lean_ctor_set(v___x_3487_, 4, v___f_3482_);
lean_ctor_set_uint8(v___x_3487_, sizeof(void*)*5, v___x_3481_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget(lean_object* v_mvarId_3488_, lean_object* v_maxSteps_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_3493_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; lean_object* v_maxDischargeDepth_3498_; uint8_t v_contextual_3499_; uint8_t v_memoize_3500_; uint8_t v_singlePass_3501_; uint8_t v_zeta_3502_; uint8_t v_beta_3503_; uint8_t v_eta_3504_; uint8_t v_etaStruct_3505_; uint8_t v_iota_3506_; uint8_t v_proj_3507_; uint8_t v_decide_3508_; uint8_t v_arith_3509_; uint8_t v_autoUnfold_3510_; uint8_t v_dsimp_3511_; uint8_t v_failIfUnchanged_3512_; uint8_t v_ground_3513_; uint8_t v_unfoldPartialApp_3514_; uint8_t v_zetaDelta_3515_; uint8_t v_index_3516_; uint8_t v_implicitDefEqProofs_3517_; uint8_t v_zetaUnused_3518_; uint8_t v_catchRuntime_3519_; uint8_t v_zetaHave_3520_; uint8_t v_letToHave_3521_; uint8_t v_congrConsts_3522_; uint8_t v_bitVecOfNat_3523_; uint8_t v_warnExponents_3524_; uint8_t v_suggestions_3525_; lean_object* v_maxSuggestions_3526_; uint8_t v_locals_3527_; uint8_t v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref(v___x_3495_);
v___x_3497_ = l_Lean_Meta_Simp_neutralConfig;
v_maxDischargeDepth_3498_ = lean_ctor_get(v___x_3497_, 1);
v_contextual_3499_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3);
v_memoize_3500_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 1);
v_singlePass_3501_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 2);
v_zeta_3502_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 3);
v_beta_3503_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 4);
v_eta_3504_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 5);
v_etaStruct_3505_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 6);
v_iota_3506_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 7);
v_proj_3507_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 8);
v_decide_3508_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 9);
v_arith_3509_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 10);
v_autoUnfold_3510_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 11);
v_dsimp_3511_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 12);
v_failIfUnchanged_3512_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 13);
v_ground_3513_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_3514_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 15);
v_zetaDelta_3515_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 16);
v_index_3516_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_3517_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 18);
v_zetaUnused_3518_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 19);
v_catchRuntime_3519_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 20);
v_zetaHave_3520_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 21);
v_letToHave_3521_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 22);
v_congrConsts_3522_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 23);
v_bitVecOfNat_3523_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 24);
v_warnExponents_3524_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 25);
v_suggestions_3525_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 26);
v_maxSuggestions_3526_ = lean_ctor_get(v___x_3497_, 2);
v_locals_3527_ = lean_ctor_get_uint8(v___x_3497_, sizeof(void*)*3 + 27);
v___x_3528_ = 1;
lean_inc(v_maxSuggestions_3526_);
lean_inc(v_maxDischargeDepth_3498_);
v___x_3529_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3529_, 0, v_maxSteps_3489_);
lean_ctor_set(v___x_3529_, 1, v_maxDischargeDepth_3498_);
lean_ctor_set(v___x_3529_, 2, v_maxSuggestions_3526_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3, v_contextual_3499_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 1, v_memoize_3500_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 2, v_singlePass_3501_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 3, v_zeta_3502_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 4, v_beta_3503_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 5, v_eta_3504_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 6, v_etaStruct_3505_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 7, v_iota_3506_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 8, v_proj_3507_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 9, v_decide_3508_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 10, v_arith_3509_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 11, v_autoUnfold_3510_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 12, v_dsimp_3511_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 13, v_failIfUnchanged_3512_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 14, v_ground_3513_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 15, v_unfoldPartialApp_3514_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 16, v_zetaDelta_3515_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 17, v_index_3516_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_3517_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 19, v_zetaUnused_3518_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 20, v_catchRuntime_3519_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 21, v_zetaHave_3520_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 22, v_letToHave_3521_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 23, v_congrConsts_3522_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 24, v_bitVecOfNat_3523_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 25, v_warnExponents_3524_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 26, v_suggestions_3525_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 27, v_locals_3527_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*3 + 28, v___x_3528_);
v___x_3530_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0));
v___x_3531_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3529_, v___x_3530_, v_a_3496_, v_a_3490_, v_a_3492_, v_a_3493_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref(v___x_3531_);
lean_inc(v_mvarId_3488_);
v___x_3533_ = l_Lean_MVarId_getType(v_mvarId_3488_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3535_; lean_object* v_a_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref(v___x_3533_);
v___x_3535_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_a_3534_, v_a_3491_);
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc_n(v_a_3536_, 2);
lean_dec_ref(v___x_3535_);
v___x_3537_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11);
v___x_3538_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12);
v___x_3539_ = l_Lean_Meta_Simp_main(v_a_3536_, v_a_3532_, v___x_3537_, v___x_3538_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v_fst_3541_; lean_object* v___x_3542_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref(v___x_3539_);
v_fst_3541_ = lean_ctor_get(v_a_3540_, 0);
lean_inc(v_fst_3541_);
lean_dec(v_a_3540_);
v___x_3542_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_3488_, v_a_3536_, v_fst_3541_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
lean_dec(v_a_3536_);
return v___x_3542_;
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec(v_a_3536_);
lean_dec(v_mvarId_3488_);
v_a_3543_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3539_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3539_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec(v_a_3532_);
lean_dec(v_mvarId_3488_);
v_a_3551_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3533_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3533_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec(v_mvarId_3488_);
v_a_3559_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3531_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3531_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v_maxSteps_3489_);
lean_dec(v_mvarId_3488_);
v_a_3567_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3495_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3495_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___boxed(lean_object* v_mvarId_3575_, lean_object* v_maxSteps_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget(v_mvarId_3575_, v_maxSteps_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(lean_object* v_mvarId_3583_, lean_object* v_x_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3583_, v_x_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3590_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
v_a_3599_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3590_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3590_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg___boxed(lean_object* v_mvarId_3607_, lean_object* v_x_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(v_mvarId_3607_, v_x_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0(lean_object* v_00_u03b1_3615_, lean_object* v_mvarId_3616_, lean_object* v_x_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(v_mvarId_3616_, v_x_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___boxed(lean_object* v_00_u03b1_3624_, lean_object* v_mvarId_3625_, lean_object* v_x_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0(v_00_u03b1_3624_, v_mvarId_3625_, v_x_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4(lean_object* v_maxSteps_3633_, lean_object* v_fvarId_3634_, lean_object* v___f_3635_, lean_object* v___f_3636_, lean_object* v___f_3637_, lean_object* v___f_3638_, lean_object* v_goal_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_3643_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3647_; lean_object* v_maxDischargeDepth_3648_; uint8_t v_contextual_3649_; uint8_t v_memoize_3650_; uint8_t v_singlePass_3651_; uint8_t v_zeta_3652_; uint8_t v_beta_3653_; uint8_t v_eta_3654_; uint8_t v_etaStruct_3655_; uint8_t v_iota_3656_; uint8_t v_proj_3657_; uint8_t v_decide_3658_; uint8_t v_arith_3659_; uint8_t v_autoUnfold_3660_; uint8_t v_dsimp_3661_; uint8_t v_failIfUnchanged_3662_; uint8_t v_ground_3663_; uint8_t v_unfoldPartialApp_3664_; uint8_t v_zetaDelta_3665_; uint8_t v_index_3666_; uint8_t v_implicitDefEqProofs_3667_; uint8_t v_zetaUnused_3668_; uint8_t v_catchRuntime_3669_; uint8_t v_zetaHave_3670_; uint8_t v_letToHave_3671_; uint8_t v_congrConsts_3672_; uint8_t v_bitVecOfNat_3673_; uint8_t v_warnExponents_3674_; uint8_t v_suggestions_3675_; lean_object* v_maxSuggestions_3676_; uint8_t v_locals_3677_; uint8_t v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref(v___x_3645_);
v___x_3647_ = l_Lean_Meta_Simp_neutralConfig;
v_maxDischargeDepth_3648_ = lean_ctor_get(v___x_3647_, 1);
v_contextual_3649_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3);
v_memoize_3650_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 1);
v_singlePass_3651_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 2);
v_zeta_3652_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 3);
v_beta_3653_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 4);
v_eta_3654_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 5);
v_etaStruct_3655_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 6);
v_iota_3656_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 7);
v_proj_3657_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 8);
v_decide_3658_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 9);
v_arith_3659_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 10);
v_autoUnfold_3660_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 11);
v_dsimp_3661_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 12);
v_failIfUnchanged_3662_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 13);
v_ground_3663_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_3664_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 15);
v_zetaDelta_3665_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 16);
v_index_3666_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_3667_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 18);
v_zetaUnused_3668_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 19);
v_catchRuntime_3669_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 20);
v_zetaHave_3670_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 21);
v_letToHave_3671_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 22);
v_congrConsts_3672_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 23);
v_bitVecOfNat_3673_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 24);
v_warnExponents_3674_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 25);
v_suggestions_3675_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 26);
v_maxSuggestions_3676_ = lean_ctor_get(v___x_3647_, 2);
v_locals_3677_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*3 + 27);
v___x_3678_ = 1;
lean_inc(v_maxSuggestions_3676_);
lean_inc(v_maxDischargeDepth_3648_);
v___x_3679_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3679_, 0, v_maxSteps_3633_);
lean_ctor_set(v___x_3679_, 1, v_maxDischargeDepth_3648_);
lean_ctor_set(v___x_3679_, 2, v_maxSuggestions_3676_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3, v_contextual_3649_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 1, v_memoize_3650_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 2, v_singlePass_3651_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 3, v_zeta_3652_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 4, v_beta_3653_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 5, v_eta_3654_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 6, v_etaStruct_3655_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 7, v_iota_3656_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 8, v_proj_3657_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 9, v_decide_3658_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 10, v_arith_3659_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 11, v_autoUnfold_3660_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 12, v_dsimp_3661_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 13, v_failIfUnchanged_3662_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 14, v_ground_3663_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 15, v_unfoldPartialApp_3664_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 16, v_zetaDelta_3665_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 17, v_index_3666_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_3667_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 19, v_zetaUnused_3668_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 20, v_catchRuntime_3669_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 21, v_zetaHave_3670_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 22, v_letToHave_3671_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 23, v_congrConsts_3672_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 24, v_bitVecOfNat_3673_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 25, v_warnExponents_3674_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 26, v_suggestions_3675_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 27, v_locals_3677_);
lean_ctor_set_uint8(v___x_3679_, sizeof(void*)*3 + 28, v___x_3678_);
v___x_3680_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0));
v___x_3681_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3679_, v___x_3680_, v_a_3646_, v___y_3640_, v___y_3642_, v___y_3643_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3683_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref(v___x_3681_);
lean_inc(v_fvarId_3634_);
v___x_3683_ = l_Lean_FVarId_getType___redArg(v_fvarId_3634_, v___y_3640_, v___y_3642_, v___y_3643_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3685_; lean_object* v_a_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref(v___x_3683_);
v___x_3685_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_a_3684_, v___y_3641_);
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref(v___x_3685_);
v___x_3687_ = lean_unsigned_to_nat(32u);
v___x_3688_ = lean_mk_empty_array_with_capacity(v___x_3687_);
lean_dec_ref(v___x_3688_);
v___x_3689_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11);
v___x_3690_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed), 9, 0);
v___x_3691_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3691_, 0, v___f_3635_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
lean_ctor_set(v___x_3691_, 2, v___f_3636_);
lean_ctor_set(v___x_3691_, 3, v___f_3637_);
lean_ctor_set(v___x_3691_, 4, v___f_3638_);
lean_ctor_set_uint8(v___x_3691_, sizeof(void*)*5, v___x_3678_);
v___x_3692_ = l_Lean_Meta_Simp_main(v_a_3686_, v_a_3682_, v___x_3689_, v___x_3691_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v_fst_3694_; uint8_t v___x_3695_; lean_object* v___x_3696_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref(v___x_3692_);
v_fst_3694_ = lean_ctor_get(v_a_3693_, 0);
lean_inc(v_fst_3694_);
lean_dec(v_a_3693_);
v___x_3695_ = 0;
v___x_3696_ = l_Lean_Meta_applySimpResultToLocalDecl(v_goal_3639_, v_fvarId_3634_, v_fst_3694_, v___x_3695_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3717_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3699_ = v___x_3696_;
v_isShared_3700_ = v_isSharedCheck_3717_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3696_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3717_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
if (lean_obj_tag(v_a_3697_) == 0)
{
lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3701_ = lean_box(0);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3701_);
v___x_3703_ = v___x_3699_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
else
{
lean_object* v_val_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3716_; 
v_val_3705_ = lean_ctor_get(v_a_3697_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v_a_3697_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3707_ = v_a_3697_;
v_isShared_3708_ = v_isSharedCheck_3716_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_val_3705_);
lean_dec(v_a_3697_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3716_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v_snd_3709_; lean_object* v___x_3711_; 
v_snd_3709_ = lean_ctor_get(v_val_3705_, 1);
lean_inc(v_snd_3709_);
lean_dec(v_val_3705_);
if (v_isShared_3708_ == 0)
{
lean_ctor_set(v___x_3707_, 0, v_snd_3709_);
v___x_3711_ = v___x_3707_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_snd_3709_);
v___x_3711_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3713_; 
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3711_);
v___x_3713_ = v___x_3699_;
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
}
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
v_a_3718_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3696_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3696_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_dec(v_goal_3639_);
lean_dec(v_fvarId_3634_);
v_a_3726_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3692_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3692_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec(v_a_3682_);
lean_dec(v_goal_3639_);
lean_dec_ref(v___f_3638_);
lean_dec_ref(v___f_3637_);
lean_dec_ref(v___f_3636_);
lean_dec_ref(v___f_3635_);
lean_dec(v_fvarId_3634_);
v_a_3734_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3683_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3683_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec(v_goal_3639_);
lean_dec_ref(v___f_3638_);
lean_dec_ref(v___f_3637_);
lean_dec_ref(v___f_3636_);
lean_dec_ref(v___f_3635_);
lean_dec(v_fvarId_3634_);
v_a_3742_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3681_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3681_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec(v_goal_3639_);
lean_dec_ref(v___f_3638_);
lean_dec_ref(v___f_3637_);
lean_dec_ref(v___f_3636_);
lean_dec_ref(v___f_3635_);
lean_dec(v_fvarId_3634_);
lean_dec(v_maxSteps_3633_);
v_a_3750_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3645_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3645_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4___boxed(lean_object* v_maxSteps_3758_, lean_object* v_fvarId_3759_, lean_object* v___f_3760_, lean_object* v___f_3761_, lean_object* v___f_3762_, lean_object* v___f_3763_, lean_object* v_goal_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4(v_maxSteps_3758_, v_fvarId_3759_, v___f_3760_, v___f_3761_, v___f_3762_, v___f_3763_, v_goal_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(lean_object* v_goal_3771_, lean_object* v_fvarId_3772_, lean_object* v_maxSteps_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_){
_start:
{
lean_object* v___f_3779_; lean_object* v___f_3780_; lean_object* v___f_3781_; lean_object* v___f_3782_; lean_object* v___f_3783_; lean_object* v___x_3784_; 
v___f_3779_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4));
v___f_3780_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3));
v___f_3781_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2));
v___f_3782_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1));
lean_inc(v_goal_3771_);
v___f_3783_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4___boxed), 12, 7);
lean_closure_set(v___f_3783_, 0, v_maxSteps_3773_);
lean_closure_set(v___f_3783_, 1, v_fvarId_3772_);
lean_closure_set(v___f_3783_, 2, v___f_3782_);
lean_closure_set(v___f_3783_, 3, v___f_3781_);
lean_closure_set(v___f_3783_, 4, v___f_3780_);
lean_closure_set(v___f_3783_, 5, v___f_3779_);
lean_closure_set(v___f_3783_, 6, v_goal_3771_);
v___x_3784_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(v_goal_3771_, v___f_3783_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___boxed(lean_object* v_goal_3785_, lean_object* v_fvarId_3786_, lean_object* v_maxSteps_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(v_goal_3785_, v_fvarId_3786_, v_maxSteps_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
lean_dec(v_a_3791_);
lean_dec_ref(v_a_3790_);
lean_dec(v_a_3789_);
lean_dec_ref(v_a_3788_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(lean_object* v_x_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; 
lean_inc(v___y_3796_);
lean_inc_ref(v___y_3795_);
v___x_3802_ = lean_apply_7(v_x_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, lean_box(0));
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed(lean_object* v_x_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(v_x_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(lean_object* v_mvarId_3812_, lean_object* v_x_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v___f_3821_; lean_object* v___x_3822_; 
lean_inc(v___y_3815_);
lean_inc_ref(v___y_3814_);
v___f_3821_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3821_, 0, v_x_3813_);
lean_closure_set(v___f_3821_, 1, v___y_3814_);
lean_closure_set(v___f_3821_, 2, v___y_3815_);
v___x_3822_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3812_, v___f_3821_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3822_) == 0)
{
return v___x_3822_;
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3822_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3822_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___boxed(lean_object* v_mvarId_3831_, lean_object* v_x_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_mvarId_3831_, v_x_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4(lean_object* v_00_u03b1_3841_, lean_object* v_mvarId_3842_, lean_object* v_x_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_mvarId_3842_, v_x_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___boxed(lean_object* v_00_u03b1_3852_, lean_object* v_mvarId_3853_, lean_object* v_x_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4(v_00_u03b1_3852_, v_mvarId_3853_, v_x_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
return v_res_3862_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(lean_object* v_a_3863_, lean_object* v_x_3864_){
_start:
{
if (lean_obj_tag(v_x_3864_) == 0)
{
uint8_t v___x_3865_; 
v___x_3865_ = 0;
return v___x_3865_;
}
else
{
lean_object* v_key_3866_; lean_object* v_tail_3867_; uint8_t v___x_3868_; 
v_key_3866_ = lean_ctor_get(v_x_3864_, 0);
v_tail_3867_ = lean_ctor_get(v_x_3864_, 2);
v___x_3868_ = l_Lean_instBEqFVarId_beq(v_key_3866_, v_a_3863_);
if (v___x_3868_ == 0)
{
v_x_3864_ = v_tail_3867_;
goto _start;
}
else
{
return v___x_3868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg___boxed(lean_object* v_a_3870_, lean_object* v_x_3871_){
_start:
{
uint8_t v_res_3872_; lean_object* v_r_3873_; 
v_res_3872_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3870_, v_x_3871_);
lean_dec(v_x_3871_);
lean_dec(v_a_3870_);
v_r_3873_ = lean_box(v_res_3872_);
return v_r_3873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_x_3874_, lean_object* v_x_3875_){
_start:
{
if (lean_obj_tag(v_x_3875_) == 0)
{
return v_x_3874_;
}
else
{
lean_object* v_key_3876_; lean_object* v_value_3877_; lean_object* v_tail_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3901_; 
v_key_3876_ = lean_ctor_get(v_x_3875_, 0);
v_value_3877_ = lean_ctor_get(v_x_3875_, 1);
v_tail_3878_ = lean_ctor_get(v_x_3875_, 2);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_x_3875_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3880_ = v_x_3875_;
v_isShared_3881_ = v_isSharedCheck_3901_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_tail_3878_);
lean_inc(v_value_3877_);
lean_inc(v_key_3876_);
lean_dec(v_x_3875_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3901_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; uint64_t v___x_3883_; uint64_t v___x_3884_; uint64_t v___x_3885_; uint64_t v_fold_3886_; uint64_t v___x_3887_; uint64_t v___x_3888_; uint64_t v___x_3889_; size_t v___x_3890_; size_t v___x_3891_; size_t v___x_3892_; size_t v___x_3893_; size_t v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3897_; 
v___x_3882_ = lean_array_get_size(v_x_3874_);
v___x_3883_ = l_Lean_instHashableFVarId_hash(v_key_3876_);
v___x_3884_ = 32ULL;
v___x_3885_ = lean_uint64_shift_right(v___x_3883_, v___x_3884_);
v_fold_3886_ = lean_uint64_xor(v___x_3883_, v___x_3885_);
v___x_3887_ = 16ULL;
v___x_3888_ = lean_uint64_shift_right(v_fold_3886_, v___x_3887_);
v___x_3889_ = lean_uint64_xor(v_fold_3886_, v___x_3888_);
v___x_3890_ = lean_uint64_to_usize(v___x_3889_);
v___x_3891_ = lean_usize_of_nat(v___x_3882_);
v___x_3892_ = ((size_t)1ULL);
v___x_3893_ = lean_usize_sub(v___x_3891_, v___x_3892_);
v___x_3894_ = lean_usize_land(v___x_3890_, v___x_3893_);
v___x_3895_ = lean_array_uget_borrowed(v_x_3874_, v___x_3894_);
lean_inc(v___x_3895_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 2, v___x_3895_);
v___x_3897_ = v___x_3880_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_key_3876_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v_value_3877_);
lean_ctor_set(v_reuseFailAlloc_3900_, 2, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3898_; 
v___x_3898_ = lean_array_uset(v_x_3874_, v___x_3894_, v___x_3897_);
v_x_3874_ = v___x_3898_;
v_x_3875_ = v_tail_3878_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(lean_object* v_i_3902_, lean_object* v_source_3903_, lean_object* v_target_3904_){
_start:
{
lean_object* v___x_3905_; uint8_t v___x_3906_; 
v___x_3905_ = lean_array_get_size(v_source_3903_);
v___x_3906_ = lean_nat_dec_lt(v_i_3902_, v___x_3905_);
if (v___x_3906_ == 0)
{
lean_dec_ref(v_source_3903_);
lean_dec(v_i_3902_);
return v_target_3904_;
}
else
{
lean_object* v_es_3907_; lean_object* v___x_3908_; lean_object* v_source_3909_; lean_object* v_target_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_es_3907_ = lean_array_fget(v_source_3903_, v_i_3902_);
v___x_3908_ = lean_box(0);
v_source_3909_ = lean_array_fset(v_source_3903_, v_i_3902_, v___x_3908_);
v_target_3910_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(v_target_3904_, v_es_3907_);
v___x_3911_ = lean_unsigned_to_nat(1u);
v___x_3912_ = lean_nat_add(v_i_3902_, v___x_3911_);
lean_dec(v_i_3902_);
v_i_3902_ = v___x_3912_;
v_source_3903_ = v_source_3909_;
v_target_3904_ = v_target_3910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(lean_object* v_data_3914_){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v_nbuckets_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3915_ = lean_array_get_size(v_data_3914_);
v___x_3916_ = lean_unsigned_to_nat(2u);
v_nbuckets_3917_ = lean_nat_mul(v___x_3915_, v___x_3916_);
v___x_3918_ = lean_unsigned_to_nat(0u);
v___x_3919_ = lean_box(0);
v___x_3920_ = lean_mk_array(v_nbuckets_3917_, v___x_3919_);
v___x_3921_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(v___x_3918_, v_data_3914_, v___x_3920_);
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_m_3922_, lean_object* v_a_3923_, lean_object* v_b_3924_){
_start:
{
lean_object* v_size_3925_; lean_object* v_buckets_3926_; lean_object* v___x_3927_; uint64_t v___x_3928_; uint64_t v___x_3929_; uint64_t v___x_3930_; uint64_t v_fold_3931_; uint64_t v___x_3932_; uint64_t v___x_3933_; uint64_t v___x_3934_; size_t v___x_3935_; size_t v___x_3936_; size_t v___x_3937_; size_t v___x_3938_; size_t v___x_3939_; lean_object* v_bkt_3940_; uint8_t v___x_3941_; 
v_size_3925_ = lean_ctor_get(v_m_3922_, 0);
v_buckets_3926_ = lean_ctor_get(v_m_3922_, 1);
v___x_3927_ = lean_array_get_size(v_buckets_3926_);
v___x_3928_ = l_Lean_instHashableFVarId_hash(v_a_3923_);
v___x_3929_ = 32ULL;
v___x_3930_ = lean_uint64_shift_right(v___x_3928_, v___x_3929_);
v_fold_3931_ = lean_uint64_xor(v___x_3928_, v___x_3930_);
v___x_3932_ = 16ULL;
v___x_3933_ = lean_uint64_shift_right(v_fold_3931_, v___x_3932_);
v___x_3934_ = lean_uint64_xor(v_fold_3931_, v___x_3933_);
v___x_3935_ = lean_uint64_to_usize(v___x_3934_);
v___x_3936_ = lean_usize_of_nat(v___x_3927_);
v___x_3937_ = ((size_t)1ULL);
v___x_3938_ = lean_usize_sub(v___x_3936_, v___x_3937_);
v___x_3939_ = lean_usize_land(v___x_3935_, v___x_3938_);
v_bkt_3940_ = lean_array_uget_borrowed(v_buckets_3926_, v___x_3939_);
v___x_3941_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3923_, v_bkt_3940_);
if (v___x_3941_ == 0)
{
lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3962_; 
lean_inc_ref(v_buckets_3926_);
lean_inc(v_size_3925_);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_m_3922_);
if (v_isSharedCheck_3962_ == 0)
{
lean_object* v_unused_3963_; lean_object* v_unused_3964_; 
v_unused_3963_ = lean_ctor_get(v_m_3922_, 1);
lean_dec(v_unused_3963_);
v_unused_3964_ = lean_ctor_get(v_m_3922_, 0);
lean_dec(v_unused_3964_);
v___x_3943_ = v_m_3922_;
v_isShared_3944_ = v_isSharedCheck_3962_;
goto v_resetjp_3942_;
}
else
{
lean_dec(v_m_3922_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3962_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3945_; lean_object* v_size_x27_3946_; lean_object* v___x_3947_; lean_object* v_buckets_x27_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
v___x_3945_ = lean_unsigned_to_nat(1u);
v_size_x27_3946_ = lean_nat_add(v_size_3925_, v___x_3945_);
lean_dec(v_size_3925_);
lean_inc(v_bkt_3940_);
v___x_3947_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3947_, 0, v_a_3923_);
lean_ctor_set(v___x_3947_, 1, v_b_3924_);
lean_ctor_set(v___x_3947_, 2, v_bkt_3940_);
v_buckets_x27_3948_ = lean_array_uset(v_buckets_3926_, v___x_3939_, v___x_3947_);
v___x_3949_ = lean_unsigned_to_nat(4u);
v___x_3950_ = lean_nat_mul(v_size_x27_3946_, v___x_3949_);
v___x_3951_ = lean_unsigned_to_nat(3u);
v___x_3952_ = lean_nat_div(v___x_3950_, v___x_3951_);
lean_dec(v___x_3950_);
v___x_3953_ = lean_array_get_size(v_buckets_x27_3948_);
v___x_3954_ = lean_nat_dec_le(v___x_3952_, v___x_3953_);
lean_dec(v___x_3952_);
if (v___x_3954_ == 0)
{
lean_object* v_val_3955_; lean_object* v___x_3957_; 
v_val_3955_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(v_buckets_x27_3948_);
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 1, v_val_3955_);
lean_ctor_set(v___x_3943_, 0, v_size_x27_3946_);
v___x_3957_ = v___x_3943_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_size_x27_3946_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v_val_3955_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
else
{
lean_object* v___x_3960_; 
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 1, v_buckets_x27_3948_);
lean_ctor_set(v___x_3943_, 0, v_size_x27_3946_);
v___x_3960_ = v___x_3943_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_size_x27_3946_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_buckets_x27_3948_);
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
else
{
lean_dec(v_b_3924_);
lean_dec(v_a_3923_);
return v_m_3922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(lean_object* v_as_3965_, size_t v_i_3966_, size_t v_stop_3967_, lean_object* v_b_3968_, lean_object* v___y_3969_){
_start:
{
uint8_t v___x_3971_; 
v___x_3971_ = lean_usize_dec_eq(v_i_3966_, v_stop_3967_);
if (v___x_3971_ == 0)
{
lean_object* v___x_3972_; lean_object* v_rewriteCache_3973_; lean_object* v_acNfCache_3974_; lean_object* v_typeAnalysis_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3989_; 
v___x_3972_ = lean_st_ref_take(v___y_3969_);
v_rewriteCache_3973_ = lean_ctor_get(v___x_3972_, 0);
v_acNfCache_3974_ = lean_ctor_get(v___x_3972_, 1);
v_typeAnalysis_3975_ = lean_ctor_get(v___x_3972_, 2);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3977_ = v___x_3972_;
v_isShared_3978_ = v_isSharedCheck_3989_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_typeAnalysis_3975_);
lean_inc(v_acNfCache_3974_);
lean_inc(v_rewriteCache_3973_);
lean_dec(v___x_3972_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3989_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3983_; 
v___x_3979_ = lean_array_uget_borrowed(v_as_3965_, v_i_3966_);
v___x_3980_ = lean_box(0);
lean_inc(v___x_3979_);
v___x_3981_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(v_acNfCache_3974_, v___x_3979_, v___x_3980_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 1, v___x_3981_);
v___x_3983_ = v___x_3977_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_rewriteCache_3973_);
lean_ctor_set(v_reuseFailAlloc_3988_, 1, v___x_3981_);
lean_ctor_set(v_reuseFailAlloc_3988_, 2, v_typeAnalysis_3975_);
v___x_3983_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3984_; size_t v___x_3985_; size_t v___x_3986_; 
v___x_3984_ = lean_st_ref_set(v___y_3969_, v___x_3983_);
v___x_3985_ = ((size_t)1ULL);
v___x_3986_ = lean_usize_add(v_i_3966_, v___x_3985_);
v_i_3966_ = v___x_3986_;
v_b_3968_ = v___x_3980_;
goto _start;
}
}
}
else
{
lean_object* v___x_3990_; 
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v_b_3968_);
return v___x_3990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg___boxed(lean_object* v_as_3991_, lean_object* v_i_3992_, lean_object* v_stop_3993_, lean_object* v_b_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
size_t v_i_boxed_3997_; size_t v_stop_boxed_3998_; lean_object* v_res_3999_; 
v_i_boxed_3997_ = lean_unbox_usize(v_i_3992_);
lean_dec(v_i_3992_);
v_stop_boxed_3998_ = lean_unbox_usize(v_stop_3993_);
lean_dec(v_stop_3993_);
v_res_3999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_as_3991_, v_i_boxed_3997_, v_stop_boxed_3998_, v_b_3994_, v___y_3995_);
lean_dec(v___y_3995_);
lean_dec_ref(v_as_3991_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0(lean_object* v___x_4000_, size_t v___x_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_Meta_getPropHyps(v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4028_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4028_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4028_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; uint8_t v___x_4016_; 
v___x_4014_ = lean_array_get_size(v_a_4010_);
v___x_4015_ = lean_box(0);
v___x_4016_ = lean_nat_dec_lt(v___x_4000_, v___x_4014_);
if (v___x_4016_ == 0)
{
lean_object* v___x_4018_; 
lean_dec(v_a_4010_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4015_);
v___x_4018_ = v___x_4012_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4015_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
else
{
uint8_t v___x_4020_; 
v___x_4020_ = lean_nat_dec_le(v___x_4014_, v___x_4014_);
if (v___x_4020_ == 0)
{
if (v___x_4016_ == 0)
{
lean_object* v___x_4022_; 
lean_dec(v_a_4010_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4015_);
v___x_4022_ = v___x_4012_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v___x_4015_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
else
{
size_t v___x_4024_; lean_object* v___x_4025_; 
lean_del_object(v___x_4012_);
v___x_4024_ = lean_usize_of_nat(v___x_4014_);
v___x_4025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_a_4010_, v___x_4001_, v___x_4024_, v___x_4015_, v___y_4003_);
lean_dec(v_a_4010_);
return v___x_4025_;
}
}
else
{
size_t v___x_4026_; lean_object* v___x_4027_; 
lean_del_object(v___x_4012_);
v___x_4026_ = lean_usize_of_nat(v___x_4014_);
v___x_4027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_a_4010_, v___x_4001_, v___x_4026_, v___x_4015_, v___y_4003_);
lean_dec(v_a_4010_);
return v___x_4027_;
}
}
}
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
v_a_4029_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4009_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4009_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v___x_4037_, lean_object* v___x_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
size_t v___x_8305__boxed_4046_; lean_object* v_res_4047_; 
v___x_8305__boxed_4046_ = lean_unbox_usize(v___x_4038_);
lean_dec(v___x_4038_);
v_res_4047_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0(v___x_4037_, v___x_8305__boxed_4046_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___x_4037_);
return v_res_4047_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_m_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v_buckets_4050_; lean_object* v___x_4051_; uint64_t v___x_4052_; uint64_t v___x_4053_; uint64_t v___x_4054_; uint64_t v_fold_4055_; uint64_t v___x_4056_; uint64_t v___x_4057_; uint64_t v___x_4058_; size_t v___x_4059_; size_t v___x_4060_; size_t v___x_4061_; size_t v___x_4062_; size_t v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; 
v_buckets_4050_ = lean_ctor_get(v_m_4048_, 1);
v___x_4051_ = lean_array_get_size(v_buckets_4050_);
v___x_4052_ = l_Lean_instHashableFVarId_hash(v_a_4049_);
v___x_4053_ = 32ULL;
v___x_4054_ = lean_uint64_shift_right(v___x_4052_, v___x_4053_);
v_fold_4055_ = lean_uint64_xor(v___x_4052_, v___x_4054_);
v___x_4056_ = 16ULL;
v___x_4057_ = lean_uint64_shift_right(v_fold_4055_, v___x_4056_);
v___x_4058_ = lean_uint64_xor(v_fold_4055_, v___x_4057_);
v___x_4059_ = lean_uint64_to_usize(v___x_4058_);
v___x_4060_ = lean_usize_of_nat(v___x_4051_);
v___x_4061_ = ((size_t)1ULL);
v___x_4062_ = lean_usize_sub(v___x_4060_, v___x_4061_);
v___x_4063_ = lean_usize_land(v___x_4059_, v___x_4062_);
v___x_4064_ = lean_array_uget_borrowed(v_buckets_4050_, v___x_4063_);
v___x_4065_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_4049_, v___x_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_m_4066_, lean_object* v_a_4067_){
_start:
{
uint8_t v_res_4068_; lean_object* v_r_4069_; 
v_res_4068_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(v_m_4066_, v_a_4067_);
lean_dec(v_a_4067_);
lean_dec_ref(v_m_4066_);
v_r_4069_ = lean_box(v_res_4068_);
return v_r_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(lean_object* v_as_4070_, size_t v_i_4071_, size_t v_stop_4072_, lean_object* v_b_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v_a_4077_; uint8_t v___x_4081_; 
v___x_4081_ = lean_usize_dec_eq(v_i_4071_, v_stop_4072_);
if (v___x_4081_ == 0)
{
lean_object* v___x_4082_; lean_object* v_acNfCache_4083_; lean_object* v___x_4084_; uint8_t v___x_4085_; 
v___x_4082_ = lean_st_ref_get(v___y_4074_);
v_acNfCache_4083_ = lean_ctor_get(v___x_4082_, 1);
lean_inc_ref(v_acNfCache_4083_);
lean_dec(v___x_4082_);
v___x_4084_ = lean_array_uget_borrowed(v_as_4070_, v_i_4071_);
v___x_4085_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(v_acNfCache_4083_, v___x_4084_);
lean_dec_ref(v_acNfCache_4083_);
if (v___x_4085_ == 0)
{
lean_object* v___x_4086_; 
lean_inc(v___x_4084_);
v___x_4086_ = lean_array_push(v_b_4073_, v___x_4084_);
v_a_4077_ = v___x_4086_;
goto v___jp_4076_;
}
else
{
v_a_4077_ = v_b_4073_;
goto v___jp_4076_;
}
}
else
{
lean_object* v___x_4087_; 
v___x_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4087_, 0, v_b_4073_);
return v___x_4087_;
}
v___jp_4076_:
{
size_t v___x_4078_; size_t v___x_4079_; 
v___x_4078_ = ((size_t)1ULL);
v___x_4079_ = lean_usize_add(v_i_4071_, v___x_4078_);
v_i_4071_ = v___x_4079_;
v_b_4073_ = v_a_4077_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg___boxed(lean_object* v_as_4088_, lean_object* v_i_4089_, lean_object* v_stop_4090_, lean_object* v_b_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
size_t v_i_boxed_4094_; size_t v_stop_boxed_4095_; lean_object* v_res_4096_; 
v_i_boxed_4094_ = lean_unbox_usize(v_i_4089_);
lean_dec(v_i_4089_);
v_stop_boxed_4095_ = lean_unbox_usize(v_stop_4090_);
lean_dec(v_stop_4090_);
v_res_4096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_as_4088_, v_i_boxed_4094_, v_stop_boxed_4095_, v_b_4091_, v___y_4092_);
lean_dec(v___y_4092_);
lean_dec_ref(v_as_4088_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_as_4097_, size_t v_sz_4098_, size_t v_i_4099_, lean_object* v_b_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
uint8_t v___x_4107_; 
v___x_4107_ = lean_usize_dec_lt(v_i_4099_, v_sz_4098_);
if (v___x_4107_ == 0)
{
lean_object* v___x_4108_; 
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v_b_4100_);
return v___x_4108_;
}
else
{
lean_object* v_maxSteps_4109_; lean_object* v_a_4110_; lean_object* v___x_4111_; 
v_maxSteps_4109_ = lean_ctor_get(v___y_4101_, 1);
v_a_4110_ = lean_array_uget_borrowed(v_as_4097_, v_i_4099_);
lean_inc(v_maxSteps_4109_);
lean_inc(v_a_4110_);
lean_inc(v_b_4100_);
v___x_4111_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(v_b_4100_, v_a_4110_, v_maxSteps_4109_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v_a_4114_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref(v___x_4111_);
if (lean_obj_tag(v_a_4112_) == 1)
{
lean_object* v_val_4118_; 
lean_dec(v_b_4100_);
v_val_4118_ = lean_ctor_get(v_a_4112_, 0);
lean_inc(v_val_4118_);
lean_dec_ref(v_a_4112_);
v_a_4114_ = v_val_4118_;
goto v___jp_4113_;
}
else
{
lean_dec(v_a_4112_);
v_a_4114_ = v_b_4100_;
goto v___jp_4113_;
}
v___jp_4113_:
{
size_t v___x_4115_; size_t v___x_4116_; 
v___x_4115_ = ((size_t)1ULL);
v___x_4116_ = lean_usize_add(v_i_4099_, v___x_4115_);
v_i_4099_ = v___x_4116_;
v_b_4100_ = v_a_4114_;
goto _start;
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_dec(v_b_4100_);
v_a_4119_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4111_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4111_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_as_4127_, lean_object* v_sz_4128_, lean_object* v_i_4129_, lean_object* v_b_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
size_t v_sz_boxed_4137_; size_t v_i_boxed_4138_; lean_object* v_res_4139_; 
v_sz_boxed_4137_ = lean_unbox_usize(v_sz_4128_);
lean_dec(v_sz_4128_);
v_i_boxed_4138_ = lean_unbox_usize(v_i_4129_);
lean_dec(v_i_4129_);
v_res_4139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(v_as_4127_, v_sz_boxed_4137_, v_i_boxed_4138_, v_b_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec_ref(v_as_4127_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1(lean_object* v_goal_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = l_Lean_Meta_getPropHyps(v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4157_; lean_object* v_a_4159_; lean_object* v___y_4192_; lean_object* v___x_4202_; lean_object* v___x_4203_; uint8_t v___x_4204_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref(v___x_4155_);
v___x_4157_ = lean_unsigned_to_nat(0u);
v___x_4202_ = lean_array_get_size(v_a_4156_);
v___x_4203_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__1));
v___x_4204_ = lean_nat_dec_lt(v___x_4157_, v___x_4202_);
if (v___x_4204_ == 0)
{
lean_dec(v_a_4156_);
v_a_4159_ = v___x_4203_;
goto v___jp_4158_;
}
else
{
uint8_t v___x_4205_; 
v___x_4205_ = lean_nat_dec_le(v___x_4202_, v___x_4202_);
if (v___x_4205_ == 0)
{
if (v___x_4204_ == 0)
{
lean_dec(v_a_4156_);
v_a_4159_ = v___x_4203_;
goto v___jp_4158_;
}
else
{
size_t v___x_4206_; size_t v___x_4207_; lean_object* v___x_4208_; 
v___x_4206_ = ((size_t)0ULL);
v___x_4207_ = lean_usize_of_nat(v___x_4202_);
v___x_4208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_a_4156_, v___x_4206_, v___x_4207_, v___x_4203_, v___y_4149_);
lean_dec(v_a_4156_);
v___y_4192_ = v___x_4208_;
goto v___jp_4191_;
}
}
else
{
size_t v___x_4209_; size_t v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = ((size_t)0ULL);
v___x_4210_ = lean_usize_of_nat(v___x_4202_);
v___x_4211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_a_4156_, v___x_4209_, v___x_4210_, v___x_4203_, v___y_4149_);
lean_dec(v_a_4156_);
v___y_4192_ = v___x_4211_;
goto v___jp_4191_;
}
}
v___jp_4158_:
{
size_t v_sz_4160_; size_t v___x_4161_; lean_object* v___x_4162_; 
v_sz_4160_ = lean_array_size(v_a_4159_);
v___x_4161_ = ((size_t)0ULL);
v___x_4162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(v_a_4159_, v_sz_4160_, v___x_4161_, v_goal_4147_, v___y_4148_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
lean_dec_ref(v_a_4159_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___f_4164_; lean_object* v___x_4165_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc_n(v_a_4163_, 2);
lean_dec_ref(v___x_4162_);
v___f_4164_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0));
v___x_4165_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_a_4163_, v___f_4164_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4173_; 
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4173_ == 0)
{
lean_object* v_unused_4174_; 
v_unused_4174_ = lean_ctor_get(v___x_4165_, 0);
lean_dec(v_unused_4174_);
v___x_4167_ = v___x_4165_;
v_isShared_4168_ = v_isSharedCheck_4173_;
goto v_resetjp_4166_;
}
else
{
lean_dec(v___x_4165_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4173_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4169_; lean_object* v___x_4171_; 
v___x_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4169_, 0, v_a_4163_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v___x_4169_);
v___x_4171_ = v___x_4167_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v___x_4169_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
lean_dec(v_a_4163_);
v_a_4175_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4165_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4165_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
v_a_4183_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4162_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4162_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
v___jp_4191_:
{
if (lean_obj_tag(v___y_4192_) == 0)
{
lean_object* v_a_4193_; 
v_a_4193_ = lean_ctor_get(v___y_4192_, 0);
lean_inc(v_a_4193_);
lean_dec_ref(v___y_4192_);
v_a_4159_ = v_a_4193_;
goto v___jp_4158_;
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec(v_goal_4147_);
v_a_4194_ = lean_ctor_get(v___y_4192_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___y_4192_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___y_4192_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___y_4192_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
else
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
lean_dec(v_goal_4147_);
v_a_4212_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___x_4155_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4155_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4212_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v_goal_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1(v_goal_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2(lean_object* v_goal_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
lean_object* v___f_4237_; lean_object* v___x_4238_; 
lean_inc(v_goal_4229_);
v___f_4237_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4237_, 0, v_goal_4229_);
v___x_4238_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_goal_4229_, v___f_4237_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2___boxed(lean_object* v_goal_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2(v_goal_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
return v_res_4247_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0(lean_object* v_00_u03b2_4256_, lean_object* v_m_4257_, lean_object* v_a_4258_){
_start:
{
uint8_t v___x_4259_; 
v___x_4259_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(v_m_4257_, v_a_4258_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_00_u03b2_4260_, lean_object* v_m_4261_, lean_object* v_a_4262_){
_start:
{
uint8_t v_res_4263_; lean_object* v_r_4264_; 
v_res_4263_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0(v_00_u03b2_4260_, v_m_4261_, v_a_4262_);
lean_dec(v_a_4262_);
lean_dec_ref(v_m_4261_);
v_r_4264_ = lean_box(v_res_4263_);
return v_r_4264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1(lean_object* v_00_u03b2_4265_, lean_object* v_m_4266_, lean_object* v_a_4267_, lean_object* v_b_4268_){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(v_m_4266_, v_a_4267_, v_b_4268_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2(lean_object* v_as_4270_, size_t v_sz_4271_, size_t v_i_4272_, lean_object* v_b_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(v_as_4270_, v_sz_4271_, v_i_4272_, v_b_4273_, v___y_4274_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_as_4282_, lean_object* v_sz_4283_, lean_object* v_i_4284_, lean_object* v_b_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
size_t v_sz_boxed_4293_; size_t v_i_boxed_4294_; lean_object* v_res_4295_; 
v_sz_boxed_4293_ = lean_unbox_usize(v_sz_4283_);
lean_dec(v_sz_4283_);
v_i_boxed_4294_ = lean_unbox_usize(v_i_4284_);
lean_dec(v_i_4284_);
v_res_4295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2(v_as_4282_, v_sz_boxed_4293_, v_i_boxed_4294_, v_b_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec_ref(v_as_4282_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3(lean_object* v_as_4296_, size_t v_i_4297_, size_t v_stop_4298_, lean_object* v_b_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v___x_4307_; 
v___x_4307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_as_4296_, v_i_4297_, v_stop_4298_, v_b_4299_, v___y_4301_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___boxed(lean_object* v_as_4308_, lean_object* v_i_4309_, lean_object* v_stop_4310_, lean_object* v_b_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
size_t v_i_boxed_4319_; size_t v_stop_boxed_4320_; lean_object* v_res_4321_; 
v_i_boxed_4319_ = lean_unbox_usize(v_i_4309_);
lean_dec(v_i_4309_);
v_stop_boxed_4320_ = lean_unbox_usize(v_stop_4310_);
lean_dec(v_stop_4310_);
v_res_4321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3(v_as_4308_, v_i_boxed_4319_, v_stop_boxed_4320_, v_b_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec_ref(v_as_4308_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5(lean_object* v_as_4322_, size_t v_i_4323_, size_t v_stop_4324_, lean_object* v_b_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_as_4322_, v_i_4323_, v_stop_4324_, v_b_4325_, v___y_4327_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___boxed(lean_object* v_as_4334_, lean_object* v_i_4335_, lean_object* v_stop_4336_, lean_object* v_b_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
size_t v_i_boxed_4345_; size_t v_stop_boxed_4346_; lean_object* v_res_4347_; 
v_i_boxed_4345_ = lean_unbox_usize(v_i_4335_);
lean_dec(v_i_4335_);
v_stop_boxed_4346_ = lean_unbox_usize(v_stop_4336_);
lean_dec(v_stop_4336_);
v_res_4347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5(v_as_4334_, v_i_boxed_4345_, v_stop_boxed_4346_, v_b_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
lean_dec(v___y_4343_);
lean_dec_ref(v___y_4342_);
lean_dec(v___y_4341_);
lean_dec_ref(v___y_4340_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec_ref(v_as_4334_);
return v_res_4347_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0(lean_object* v_00_u03b2_4348_, lean_object* v_a_4349_, lean_object* v_x_4350_){
_start:
{
uint8_t v___x_4351_; 
v___x_4351_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_4349_, v_x_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4352_, lean_object* v_a_4353_, lean_object* v_x_4354_){
_start:
{
uint8_t v_res_4355_; lean_object* v_r_4356_; 
v_res_4355_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0(v_00_u03b2_4352_, v_a_4353_, v_x_4354_);
lean_dec(v_x_4354_);
lean_dec(v_a_4353_);
v_r_4356_ = lean_box(v_res_4355_);
return v_r_4356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2(lean_object* v_00_u03b2_4357_, lean_object* v_data_4358_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(v_data_4358_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4360_, lean_object* v_i_4361_, lean_object* v_source_4362_, lean_object* v_target_4363_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(v_i_4361_, v_source_4362_, v_target_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4365_, lean_object* v_x_4366_, lean_object* v_x_4367_){
_start:
{
lean_object* v___x_4368_; 
v___x_4368_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(v_x_4366_, v_x_4367_);
return v___x_4368_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_AC_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_AC_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC(builtin);
}
#ifdef __cplusplus
}
#endif
