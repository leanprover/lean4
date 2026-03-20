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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
double lean_float_of_nat(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_merge___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Found binary operation '"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "', expected '"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "'.Treating as atom."};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "canonicalizeWithSharing"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Operations mismatch:\n      the left-hand-side has operation "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n        "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\n      but the right-hand-side has operation "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__8;
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Canonicalizing with respect to operation: '"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__13;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to recognize operation: "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Canonicalizing: "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_size_384_);
lean_inc(v_size_384_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(lean_object* v_cls_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_options_819_; uint8_t v_hasTrace_820_; 
v_options_819_ = lean_ctor_get(v___y_817_, 2);
v_hasTrace_820_ = lean_ctor_get_uint8(v_options_819_, sizeof(void*)*1);
if (v_hasTrace_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec(v_cls_815_);
v___x_821_ = lean_box(v_hasTrace_820_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___y_816_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
else
{
lean_object* v_inheritedTraceOptions_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_inheritedTraceOptions_824_ = lean_ctor_get(v___y_817_, 13);
v___x_825_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_826_ = l_Lean_Name_append(v___x_825_, v_cls_815_);
v___x_827_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_824_, v_options_819_, v___x_826_);
lean_dec(v___x_826_);
v___x_828_ = lean_box(v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___y_816_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___boxed(lean_object* v_cls_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_831_, v___y_832_, v___y_833_);
lean_dec_ref(v___y_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_836_, v___y_837_, v___y_840_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_851_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_852_; double v___x_853_; 
v___x_852_ = lean_unsigned_to_nat(0u);
v___x_853_ = lean_float_of_nat(v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1(lean_object* v_cls_857_, lean_object* v_msg_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_ref_865_; lean_object* v___x_866_; lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_912_; 
v_ref_865_ = lean_ctor_get(v___y_862_, 5);
v___x_866_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_858_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_912_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_912_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_912_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v_traceState_872_; lean_object* v_env_873_; lean_object* v_nextMacroScope_874_; lean_object* v_ngen_875_; lean_object* v_auxDeclNGen_876_; lean_object* v_cache_877_; lean_object* v_messages_878_; lean_object* v_infoState_879_; lean_object* v_snapshotTasks_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_911_; 
v___x_871_ = lean_st_ref_take(v___y_863_);
v_traceState_872_ = lean_ctor_get(v___x_871_, 4);
v_env_873_ = lean_ctor_get(v___x_871_, 0);
v_nextMacroScope_874_ = lean_ctor_get(v___x_871_, 1);
v_ngen_875_ = lean_ctor_get(v___x_871_, 2);
v_auxDeclNGen_876_ = lean_ctor_get(v___x_871_, 3);
v_cache_877_ = lean_ctor_get(v___x_871_, 5);
v_messages_878_ = lean_ctor_get(v___x_871_, 6);
v_infoState_879_ = lean_ctor_get(v___x_871_, 7);
v_snapshotTasks_880_ = lean_ctor_get(v___x_871_, 8);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_911_ == 0)
{
v___x_882_ = v___x_871_;
v_isShared_883_ = v_isSharedCheck_911_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_snapshotTasks_880_);
lean_inc(v_infoState_879_);
lean_inc(v_messages_878_);
lean_inc(v_cache_877_);
lean_inc(v_traceState_872_);
lean_inc(v_auxDeclNGen_876_);
lean_inc(v_ngen_875_);
lean_inc(v_nextMacroScope_874_);
lean_inc(v_env_873_);
lean_dec(v___x_871_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_911_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
uint64_t v_tid_884_; lean_object* v_traces_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_910_; 
v_tid_884_ = lean_ctor_get_uint64(v_traceState_872_, sizeof(void*)*1);
v_traces_885_ = lean_ctor_get(v_traceState_872_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v_traceState_872_);
if (v_isSharedCheck_910_ == 0)
{
v___x_887_ = v_traceState_872_;
v_isShared_888_ = v_isSharedCheck_910_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_traces_885_);
lean_dec(v_traceState_872_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_910_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; double v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_889_ = lean_box(0);
v___x_890_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__0);
v___x_891_ = 0;
v___x_892_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__1));
v___x_893_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_893_, 0, v_cls_857_);
lean_ctor_set(v___x_893_, 1, v___x_889_);
lean_ctor_set(v___x_893_, 2, v___x_892_);
lean_ctor_set_float(v___x_893_, sizeof(void*)*3, v___x_890_);
lean_ctor_set_float(v___x_893_, sizeof(void*)*3 + 8, v___x_890_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*3 + 16, v___x_891_);
v___x_894_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__2));
v___x_895_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v_a_867_);
lean_ctor_set(v___x_895_, 2, v___x_894_);
lean_inc(v_ref_865_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v_ref_865_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = l_Lean_PersistentArray_push___redArg(v_traces_885_, v___x_896_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_897_);
v___x_899_ = v___x_887_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_897_);
lean_ctor_set_uint64(v_reuseFailAlloc_909_, sizeof(void*)*1, v_tid_884_);
v___x_899_ = v_reuseFailAlloc_909_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 4, v___x_899_);
v___x_901_ = v___x_882_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_env_873_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_nextMacroScope_874_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v_ngen_875_);
lean_ctor_set(v_reuseFailAlloc_908_, 3, v_auxDeclNGen_876_);
lean_ctor_set(v_reuseFailAlloc_908_, 4, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_908_, 5, v_cache_877_);
lean_ctor_set(v_reuseFailAlloc_908_, 6, v_messages_878_);
lean_ctor_set(v_reuseFailAlloc_908_, 7, v_infoState_879_);
lean_ctor_set(v_reuseFailAlloc_908_, 8, v_snapshotTasks_880_);
v___x_901_ = v_reuseFailAlloc_908_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_902_ = lean_st_ref_set(v___y_863_, v___x_901_);
v___x_903_ = lean_box(0);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___y_859_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_904_);
v___x_906_ = v___x_869_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___boxed(lean_object* v_cls_913_, lean_object* v_msg_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1(v_cls_913_, v_msg_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_921_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__4));
v___x_931_ = l_Lean_stringToMessageData(v___x_930_);
return v___x_931_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__6));
v___x_934_ = l_Lean_stringToMessageData(v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__8));
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__10));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_941_, lean_object* v_coeff_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
if (lean_obj_tag(v_a_943_) == 5)
{
lean_object* v_fn_950_; 
v_fn_950_ = lean_ctor_get(v_a_943_, 0);
if (lean_obj_tag(v_fn_950_) == 5)
{
lean_object* v_arg_951_; lean_object* v_fn_952_; lean_object* v_arg_953_; uint8_t v___x_954_; 
v_arg_951_ = lean_ctor_get(v_a_943_, 1);
v_fn_952_ = lean_ctor_get(v_fn_950_, 0);
v_arg_953_ = lean_ctor_get(v_fn_950_, 1);
lean_inc_ref(v_fn_952_);
v___x_954_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_isSameKind___redArg(v_fn_952_);
if (v___x_954_ == 0)
{
lean_object* v_cls_955_; lean_object* v___x_956_; lean_object* v_a_957_; lean_object* v_fst_958_; uint8_t v___x_959_; 
v_cls_955_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_956_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_955_, v_a_944_, v_a_947_);
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref(v___x_956_);
v_fst_958_ = lean_ctor_get(v_a_957_, 0);
v___x_959_ = lean_unbox(v_fst_958_);
if (v___x_959_ == 0)
{
lean_object* v_snd_960_; lean_object* v___x_961_; 
lean_dec_ref(v_op_941_);
v_snd_960_ = lean_ctor_get(v_a_957_, 1);
lean_inc(v_snd_960_);
lean_dec(v_a_957_);
v___x_961_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_942_, v_a_943_, v_snd_960_);
return v___x_961_;
}
else
{
lean_object* v_snd_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_997_; 
v_snd_962_ = lean_ctor_get(v_a_957_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_a_957_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_a_957_, 0);
lean_dec(v_unused_998_);
v___x_964_ = v_a_957_;
v_isShared_965_ = v_isSharedCheck_997_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_snd_962_);
lean_dec(v_a_957_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_997_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_966_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__5);
lean_inc_ref(v_fn_952_);
v___x_967_ = l_Lean_MessageData_ofExpr(v_fn_952_);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 7);
lean_ctor_set(v___x_964_, 1, v___x_967_);
lean_ctor_set(v___x_964_, 0, v___x_966_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_967_);
v___x_969_ = v_reuseFailAlloc_996_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_970_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
lean_inc_ref(v_arg_953_);
v___x_972_ = l_Lean_MessageData_ofExpr(v_arg_953_);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v___x_970_);
lean_inc_ref(v_arg_951_);
v___x_975_ = l_Lean_MessageData_ofExpr(v_arg_951_);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__9);
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_op_941_);
v___x_980_ = l_Lean_MessageData_ofExpr(v___x_979_);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_978_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__11);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1(v_cls_955_, v___x_983_, v_snd_962_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v_snd_986_; lean_object* v___x_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_984_);
v_snd_986_ = lean_ctor_get(v_a_985_, 1);
lean_inc(v_snd_986_);
lean_dec(v_a_985_);
v___x_987_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_942_, v_a_943_, v_snd_986_);
return v___x_987_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v_a_943_);
lean_dec_ref(v_coeff_942_);
v_a_988_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_984_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_984_);
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
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
else
{
lean_object* v___x_999_; 
lean_inc_ref(v_arg_953_);
lean_inc_ref(v_arg_951_);
lean_dec_ref(v_a_943_);
lean_inc_ref(v_op_941_);
v___x_999_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(v_op_941_, v_coeff_942_, v_arg_953_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v_fst_1001_; lean_object* v_snd_1002_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v_fst_1001_ = lean_ctor_get(v_a_1000_, 0);
lean_inc(v_fst_1001_);
v_snd_1002_ = lean_ctor_get(v_a_1000_, 1);
lean_inc(v_snd_1002_);
lean_dec(v_a_1000_);
v_coeff_942_ = v_fst_1001_;
v_a_943_ = v_arg_951_;
v_a_944_ = v_snd_1002_;
goto _start;
}
else
{
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_op_941_);
return v___x_999_;
}
}
}
else
{
lean_object* v___x_1004_; 
lean_dec_ref(v_op_941_);
v___x_1004_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_942_, v_a_943_, v_a_944_);
return v___x_1004_;
}
}
else
{
lean_object* v___x_1005_; 
lean_dec_ref(v_op_941_);
v___x_1005_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_942_, v_a_943_, v_a_944_);
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_1006_, lean_object* v_coeff_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(v_op_1006_, v_coeff_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
return v_res_1015_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_unsigned_to_nat(16u);
v___x_1018_ = lean_mk_array(v___x_1017_, v___x_1016_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(lean_object* v_op_1022_, lean_object* v_e_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1031_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go(v_op_1022_, v___x_1030_, v_e_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_1032_, lean_object* v_e_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_op_1032_, v_e_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1041_, lean_object* v_a_1042_, lean_object* v_x_1043_){
_start:
{
if (lean_obj_tag(v_x_1043_) == 0)
{
lean_dec(v_a_1042_);
return v_x_1043_;
}
else
{
lean_object* v_key_1044_; lean_object* v_value_1045_; lean_object* v_tail_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1059_; 
v_key_1044_ = lean_ctor_get(v_x_1043_, 0);
v_value_1045_ = lean_ctor_get(v_x_1043_, 1);
v_tail_1046_ = lean_ctor_get(v_x_1043_, 2);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_x_1043_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1048_ = v_x_1043_;
v_isShared_1049_ = v_isSharedCheck_1059_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_tail_1046_);
lean_inc(v_value_1045_);
lean_inc(v_key_1044_);
lean_dec(v_x_1043_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1059_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_nat_dec_eq(v_key_1044_, v_a_1042_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1051_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1041_, v_a_1042_, v_tail_1046_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 2, v___x_1051_);
v___x_1053_ = v___x_1048_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_key_1044_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_value_1045_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
else
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
lean_dec(v_key_1044_);
v___x_1055_ = lean_nat_sub(v_value_1045_, v_commonCnt_1041_);
lean_dec(v_value_1045_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v___x_1055_);
lean_ctor_set(v___x_1048_, 0, v_a_1042_);
v___x_1057_ = v___x_1048_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1042_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_tail_1046_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1060_, lean_object* v_a_1061_, lean_object* v_x_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1060_, v_a_1061_, v_x_1062_);
lean_dec(v_commonCnt_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1064_, lean_object* v_m_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_size_1067_; lean_object* v_buckets_1068_; lean_object* v___x_1069_; uint64_t v___x_1070_; uint64_t v___x_1071_; uint64_t v___x_1072_; uint64_t v_fold_1073_; uint64_t v___x_1074_; uint64_t v___x_1075_; uint64_t v___x_1076_; size_t v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; lean_object* v_bucket_1082_; uint8_t v___x_1083_; 
v_size_1067_ = lean_ctor_get(v_m_1065_, 0);
v_buckets_1068_ = lean_ctor_get(v_m_1065_, 1);
v___x_1069_ = lean_array_get_size(v_buckets_1068_);
v___x_1070_ = lean_uint64_of_nat(v_a_1066_);
v___x_1071_ = 32ULL;
v___x_1072_ = lean_uint64_shift_right(v___x_1070_, v___x_1071_);
v_fold_1073_ = lean_uint64_xor(v___x_1070_, v___x_1072_);
v___x_1074_ = 16ULL;
v___x_1075_ = lean_uint64_shift_right(v_fold_1073_, v___x_1074_);
v___x_1076_ = lean_uint64_xor(v_fold_1073_, v___x_1075_);
v___x_1077_ = lean_uint64_to_usize(v___x_1076_);
v___x_1078_ = lean_usize_of_nat(v___x_1069_);
v___x_1079_ = ((size_t)1ULL);
v___x_1080_ = lean_usize_sub(v___x_1078_, v___x_1079_);
v___x_1081_ = lean_usize_land(v___x_1077_, v___x_1080_);
v_bucket_1082_ = lean_array_uget_borrowed(v_buckets_1068_, v___x_1081_);
v___x_1083_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1066_, v_bucket_1082_);
if (v___x_1083_ == 0)
{
lean_dec(v_a_1066_);
return v_m_1065_;
}
else
{
lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1094_; 
lean_inc(v_bucket_1082_);
lean_inc_ref(v_buckets_1068_);
lean_inc(v_size_1067_);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_m_1065_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; lean_object* v_unused_1096_; 
v_unused_1095_ = lean_ctor_get(v_m_1065_, 1);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_m_1065_, 0);
lean_dec(v_unused_1096_);
v___x_1085_ = v_m_1065_;
v_isShared_1086_ = v_isSharedCheck_1094_;
goto v_resetjp_1084_;
}
else
{
lean_dec(v_m_1065_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1094_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v_buckets_1088_; lean_object* v_bucket_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1087_ = lean_box(0);
v_buckets_1088_ = lean_array_uset(v_buckets_1068_, v___x_1081_, v___x_1087_);
v_bucket_1089_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1064_, v_a_1066_, v_bucket_1082_);
v___x_1090_ = lean_array_uset(v_buckets_1088_, v___x_1081_, v_bucket_1089_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 1, v___x_1090_);
v___x_1092_ = v___x_1085_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_size_1067_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1097_, lean_object* v_m_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1097_, v_m_1098_, v_a_1099_);
lean_dec(v_commonCnt_1097_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
if (lean_obj_tag(v_x_1102_) == 0)
{
return v_x_1101_;
}
else
{
lean_object* v_key_1103_; lean_object* v_value_1104_; lean_object* v_tail_1105_; lean_object* v___x_1106_; 
v_key_1103_ = lean_ctor_get(v_x_1102_, 0);
lean_inc(v_key_1103_);
v_value_1104_ = lean_ctor_get(v_x_1102_, 1);
lean_inc(v_value_1104_);
v_tail_1105_ = lean_ctor_get(v_x_1102_, 2);
lean_inc(v_tail_1105_);
lean_dec_ref(v_x_1102_);
v___x_1106_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(v_value_1104_, v_x_1101_, v_key_1103_);
lean_dec(v_value_1104_);
v_x_1101_ = v___x_1106_;
v_x_1102_ = v_tail_1105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
if (lean_obj_tag(v_x_1109_) == 0)
{
return v_x_1108_;
}
else
{
lean_object* v_key_1110_; lean_object* v_value_1111_; lean_object* v_tail_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v_key_1110_ = lean_ctor_get(v_x_1109_, 0);
lean_inc(v_key_1110_);
v_value_1111_ = lean_ctor_get(v_x_1109_, 1);
lean_inc(v_value_1111_);
v_tail_1112_ = lean_ctor_get(v_x_1109_, 2);
lean_inc(v_tail_1112_);
lean_dec_ref(v_x_1109_);
v___x_1113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__0(v_value_1111_, v_x_1108_, v_key_1110_);
lean_dec(v_value_1111_);
v___x_1114_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1113_, v_tail_1112_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1115_, size_t v_i_1116_, size_t v_stop_1117_, lean_object* v_b_1118_){
_start:
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_usize_dec_eq(v_i_1116_, v_stop_1117_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; size_t v___x_1122_; size_t v___x_1123_; 
v___x_1120_ = lean_array_uget_borrowed(v_as_1115_, v_i_1116_);
lean_inc(v___x_1120_);
v___x_1121_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__1(v_b_1118_, v___x_1120_);
v___x_1122_ = ((size_t)1ULL);
v___x_1123_ = lean_usize_add(v_i_1116_, v___x_1122_);
v_i_1116_ = v___x_1123_;
v_b_1118_ = v___x_1121_;
goto _start;
}
else
{
return v_b_1118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1125_, lean_object* v_i_1126_, lean_object* v_stop_1127_, lean_object* v_b_1128_){
_start:
{
size_t v_i_boxed_1129_; size_t v_stop_boxed_1130_; lean_object* v_res_1131_; 
v_i_boxed_1129_ = lean_unbox_usize(v_i_1126_);
lean_dec(v_i_1126_);
v_stop_boxed_1130_ = lean_unbox_usize(v_stop_1127_);
lean_dec(v_stop_1127_);
v_res_1131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_as_1125_, v_i_boxed_1129_, v_stop_boxed_1130_, v_b_1128_);
lean_dec_ref(v_as_1125_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1132_, lean_object* v_x_1133_){
_start:
{
if (lean_obj_tag(v_x_1133_) == 0)
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_box(0);
return v___x_1134_;
}
else
{
lean_object* v_key_1135_; lean_object* v_value_1136_; lean_object* v_tail_1137_; uint8_t v___x_1138_; 
v_key_1135_ = lean_ctor_get(v_x_1133_, 0);
v_value_1136_ = lean_ctor_get(v_x_1133_, 1);
v_tail_1137_ = lean_ctor_get(v_x_1133_, 2);
v___x_1138_ = lean_nat_dec_eq(v_key_1135_, v_a_1132_);
if (v___x_1138_ == 0)
{
v_x_1133_ = v_tail_1137_;
goto _start;
}
else
{
lean_object* v___x_1140_; 
lean_inc(v_value_1136_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_value_1136_);
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1141_, lean_object* v_x_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1141_, v_x_1142_);
lean_dec(v_x_1142_);
lean_dec(v_a_1141_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_buckets_1146_; lean_object* v___x_1147_; uint64_t v___x_1148_; uint64_t v___x_1149_; uint64_t v___x_1150_; uint64_t v_fold_1151_; uint64_t v___x_1152_; uint64_t v___x_1153_; uint64_t v___x_1154_; size_t v___x_1155_; size_t v___x_1156_; size_t v___x_1157_; size_t v___x_1158_; size_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_buckets_1146_ = lean_ctor_get(v_m_1144_, 1);
v___x_1147_ = lean_array_get_size(v_buckets_1146_);
v___x_1148_ = lean_uint64_of_nat(v_a_1145_);
v___x_1149_ = 32ULL;
v___x_1150_ = lean_uint64_shift_right(v___x_1148_, v___x_1149_);
v_fold_1151_ = lean_uint64_xor(v___x_1148_, v___x_1150_);
v___x_1152_ = 16ULL;
v___x_1153_ = lean_uint64_shift_right(v_fold_1151_, v___x_1152_);
v___x_1154_ = lean_uint64_xor(v_fold_1151_, v___x_1153_);
v___x_1155_ = lean_uint64_to_usize(v___x_1154_);
v___x_1156_ = lean_usize_of_nat(v___x_1147_);
v___x_1157_ = ((size_t)1ULL);
v___x_1158_ = lean_usize_sub(v___x_1156_, v___x_1157_);
v___x_1159_ = lean_usize_land(v___x_1155_, v___x_1158_);
v___x_1160_ = lean_array_uget_borrowed(v_buckets_1146_, v___x_1159_);
v___x_1161_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1145_, v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1162_, v_a_1163_);
lean_dec(v_a_1163_);
lean_dec_ref(v_m_1162_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1165_, lean_object* v_b_1166_, lean_object* v_x_1167_){
_start:
{
if (lean_obj_tag(v_x_1167_) == 0)
{
lean_dec(v_b_1166_);
lean_dec(v_a_1165_);
return v_x_1167_;
}
else
{
lean_object* v_key_1168_; lean_object* v_value_1169_; lean_object* v_tail_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1182_; 
v_key_1168_ = lean_ctor_get(v_x_1167_, 0);
v_value_1169_ = lean_ctor_get(v_x_1167_, 1);
v_tail_1170_ = lean_ctor_get(v_x_1167_, 2);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_x_1167_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1172_ = v_x_1167_;
v_isShared_1173_ = v_isSharedCheck_1182_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_tail_1170_);
lean_inc(v_value_1169_);
lean_inc(v_key_1168_);
lean_dec(v_x_1167_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1182_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_nat_dec_eq(v_key_1168_, v_a_1165_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1165_, v_b_1166_, v_tail_1170_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 2, v___x_1175_);
v___x_1177_ = v___x_1172_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_key_1168_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_value_1169_);
lean_ctor_set(v_reuseFailAlloc_1178_, 2, v___x_1175_);
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
lean_dec(v_value_1169_);
lean_dec(v_key_1168_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_b_1166_);
lean_ctor_set(v___x_1172_, 0, v_a_1165_);
v___x_1180_ = v___x_1172_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1165_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_b_1166_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_tail_1170_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1183_, lean_object* v_a_1184_, lean_object* v_b_1185_){
_start:
{
lean_object* v_size_1186_; lean_object* v_buckets_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1230_; 
v_size_1186_ = lean_ctor_get(v_m_1183_, 0);
v_buckets_1187_ = lean_ctor_get(v_m_1183_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_m_1183_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1189_ = v_m_1183_;
v_isShared_1190_ = v_isSharedCheck_1230_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_buckets_1187_);
lean_inc(v_size_1186_);
lean_dec(v_m_1183_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1230_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; uint64_t v___x_1192_; uint64_t v___x_1193_; uint64_t v___x_1194_; uint64_t v_fold_1195_; uint64_t v___x_1196_; uint64_t v___x_1197_; uint64_t v___x_1198_; size_t v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; size_t v___x_1202_; size_t v___x_1203_; lean_object* v_bkt_1204_; uint8_t v___x_1205_; 
v___x_1191_ = lean_array_get_size(v_buckets_1187_);
v___x_1192_ = lean_uint64_of_nat(v_a_1184_);
v___x_1193_ = 32ULL;
v___x_1194_ = lean_uint64_shift_right(v___x_1192_, v___x_1193_);
v_fold_1195_ = lean_uint64_xor(v___x_1192_, v___x_1194_);
v___x_1196_ = 16ULL;
v___x_1197_ = lean_uint64_shift_right(v_fold_1195_, v___x_1196_);
v___x_1198_ = lean_uint64_xor(v_fold_1195_, v___x_1197_);
v___x_1199_ = lean_uint64_to_usize(v___x_1198_);
v___x_1200_ = lean_usize_of_nat(v___x_1191_);
v___x_1201_ = ((size_t)1ULL);
v___x_1202_ = lean_usize_sub(v___x_1200_, v___x_1201_);
v___x_1203_ = lean_usize_land(v___x_1199_, v___x_1202_);
v_bkt_1204_ = lean_array_uget_borrowed(v_buckets_1187_, v___x_1203_);
v___x_1205_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1184_, v_bkt_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v_size_x27_1207_; lean_object* v___x_1208_; lean_object* v_buckets_x27_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1206_ = lean_unsigned_to_nat(1u);
v_size_x27_1207_ = lean_nat_add(v_size_1186_, v___x_1206_);
lean_dec(v_size_1186_);
lean_inc(v_bkt_1204_);
v___x_1208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1208_, 0, v_a_1184_);
lean_ctor_set(v___x_1208_, 1, v_b_1185_);
lean_ctor_set(v___x_1208_, 2, v_bkt_1204_);
v_buckets_x27_1209_ = lean_array_uset(v_buckets_1187_, v___x_1203_, v___x_1208_);
v___x_1210_ = lean_unsigned_to_nat(4u);
v___x_1211_ = lean_nat_mul(v_size_x27_1207_, v___x_1210_);
v___x_1212_ = lean_unsigned_to_nat(3u);
v___x_1213_ = lean_nat_div(v___x_1211_, v___x_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_array_get_size(v_buckets_x27_1209_);
v___x_1215_ = lean_nat_dec_le(v___x_1213_, v___x_1214_);
lean_dec(v___x_1213_);
if (v___x_1215_ == 0)
{
lean_object* v_val_1216_; lean_object* v___x_1218_; 
v_val_1216_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1209_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v_val_1216_);
lean_ctor_set(v___x_1189_, 0, v_size_x27_1207_);
v___x_1218_ = v___x_1189_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_size_x27_1207_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_val_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
else
{
lean_object* v___x_1221_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v_buckets_x27_1209_);
lean_ctor_set(v___x_1189_, 0, v_size_x27_1207_);
v___x_1221_ = v___x_1189_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_size_x27_1207_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_buckets_x27_1209_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
else
{
lean_object* v___x_1223_; lean_object* v_buckets_x27_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
lean_inc(v_bkt_1204_);
v___x_1223_ = lean_box(0);
v_buckets_x27_1224_ = lean_array_uset(v_buckets_1187_, v___x_1203_, v___x_1223_);
v___x_1225_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1184_, v_b_1185_, v_bkt_1204_);
v___x_1226_ = lean_array_uset(v_buckets_x27_1224_, v___x_1203_, v___x_1225_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1226_);
v___x_1228_ = v___x_1189_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_size_1186_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1231_, lean_object* v_x_1232_, lean_object* v_x_1233_){
_start:
{
if (lean_obj_tag(v_x_1233_) == 0)
{
return v_x_1232_;
}
else
{
lean_object* v_key_1234_; lean_object* v_value_1235_; lean_object* v_tail_1236_; lean_object* v___y_1238_; lean_object* v___x_1241_; 
v_key_1234_ = lean_ctor_get(v_x_1233_, 0);
lean_inc(v_key_1234_);
v_value_1235_ = lean_ctor_get(v_x_1233_, 1);
lean_inc(v_value_1235_);
v_tail_1236_ = lean_ctor_get(v_x_1233_, 2);
lean_inc(v_tail_1236_);
lean_dec_ref(v_x_1233_);
v___x_1241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1231_, v_key_1234_);
if (lean_obj_tag(v___x_1241_) == 1)
{
lean_object* v_val_1242_; uint8_t v___x_1243_; 
v_val_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_val_1242_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = lean_nat_dec_le(v_value_1235_, v_val_1242_);
if (v___x_1243_ == 0)
{
lean_dec(v_value_1235_);
v___y_1238_ = v_val_1242_;
goto v___jp_1237_;
}
else
{
lean_dec(v_val_1242_);
v___y_1238_ = v_value_1235_;
goto v___jp_1237_;
}
}
else
{
lean_dec(v___x_1241_);
lean_dec(v_value_1235_);
lean_dec(v_key_1234_);
v_x_1233_ = v_tail_1236_;
goto _start;
}
v___jp_1237_:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1232_, v_key_1234_, v___y_1238_);
v_x_1232_ = v___x_1239_;
v_x_1233_ = v_tail_1236_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(v_snd_1245_, v_x_1246_, v_x_1247_);
lean_dec_ref(v_snd_1245_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1249_, lean_object* v_as_1250_, size_t v_i_1251_, size_t v_stop_1252_, lean_object* v_b_1253_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_usize_dec_eq(v_i_1251_, v_stop_1252_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; 
v___x_1255_ = lean_array_uget_borrowed(v_as_1250_, v_i_1251_);
lean_inc(v___x_1255_);
v___x_1256_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__5(v_snd_1249_, v_b_1253_, v___x_1255_);
v___x_1257_ = ((size_t)1ULL);
v___x_1258_ = lean_usize_add(v_i_1251_, v___x_1257_);
v_i_1251_ = v___x_1258_;
v_b_1253_ = v___x_1256_;
goto _start;
}
else
{
return v_b_1253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1260_, lean_object* v_as_1261_, lean_object* v_i_1262_, lean_object* v_stop_1263_, lean_object* v_b_1264_){
_start:
{
size_t v_i_boxed_1265_; size_t v_stop_boxed_1266_; lean_object* v_res_1267_; 
v_i_boxed_1265_ = lean_unbox_usize(v_i_1262_);
lean_dec(v_i_1262_);
v_stop_boxed_1266_ = lean_unbox_usize(v_stop_1263_);
lean_dec(v_stop_1263_);
v_res_1267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(v_snd_1260_, v_as_1261_, v_i_boxed_1265_, v_stop_boxed_1266_, v_b_1264_);
lean_dec_ref(v_as_1261_);
lean_dec_ref(v_snd_1260_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1268_, lean_object* v_y_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v___y_1273_; lean_object* v_fst_1274_; lean_object* v_snd_1275_; lean_object* v_size_1279_; lean_object* v_buckets_1280_; lean_object* v_size_1281_; lean_object* v_buckets_1282_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v_buckets_1291_; lean_object* v___y_1292_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v_buckets_1307_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v_fst_1324_; lean_object* v_buckets_1325_; lean_object* v_snd_1326_; uint8_t v___x_1339_; 
v_size_1279_ = lean_ctor_get(v_y_1269_, 0);
lean_inc(v_size_1279_);
v_buckets_1280_ = lean_ctor_get(v_y_1269_, 1);
v_size_1281_ = lean_ctor_get(v_x_1268_, 0);
lean_inc(v_size_1281_);
v_buckets_1282_ = lean_ctor_get(v_x_1268_, 1);
v___x_1339_ = lean_nat_dec_lt(v_size_1279_, v_size_1281_);
if (v___x_1339_ == 0)
{
lean_inc_ref(v_buckets_1282_);
v_fst_1324_ = v_x_1268_;
v_buckets_1325_ = v_buckets_1282_;
v_snd_1326_ = v_y_1269_;
goto v___jp_1323_;
}
else
{
lean_inc_ref(v_buckets_1280_);
v_fst_1324_ = v_y_1269_;
v_buckets_1325_ = v_buckets_1280_;
v_snd_1326_ = v_x_1268_;
goto v___jp_1323_;
}
v___jp_1272_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1276_, 0, v___y_1273_);
lean_ctor_set(v___x_1276_, 1, v_fst_1274_);
lean_ctor_set(v___x_1276_, 2, v_snd_1275_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v_a_1270_);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
v___jp_1283_:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_nat_dec_lt(v_size_1279_, v_size_1281_);
lean_dec(v_size_1281_);
lean_dec(v_size_1279_);
if (v___x_1287_ == 0)
{
v___y_1273_ = v___y_1285_;
v_fst_1274_ = v___y_1284_;
v_snd_1275_ = v___y_1286_;
goto v___jp_1272_;
}
else
{
v___y_1273_ = v___y_1285_;
v_fst_1274_ = v___y_1286_;
v_snd_1275_ = v___y_1284_;
goto v___jp_1272_;
}
}
v___jp_1288_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_array_get_size(v_buckets_1291_);
v___x_1295_ = lean_nat_dec_lt(v___x_1293_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_dec_ref(v_buckets_1291_);
v___y_1284_ = v___y_1292_;
v___y_1285_ = v___y_1290_;
v___y_1286_ = v___y_1289_;
goto v___jp_1283_;
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = lean_nat_dec_le(v___x_1294_, v___x_1294_);
if (v___x_1296_ == 0)
{
if (v___x_1295_ == 0)
{
lean_dec_ref(v_buckets_1291_);
v___y_1284_ = v___y_1292_;
v___y_1285_ = v___y_1290_;
v___y_1286_ = v___y_1289_;
goto v___jp_1283_;
}
else
{
size_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = ((size_t)0ULL);
v___x_1298_ = lean_usize_of_nat(v___x_1294_);
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1291_, v___x_1297_, v___x_1298_, v___y_1289_);
lean_dec_ref(v_buckets_1291_);
v___y_1284_ = v___y_1292_;
v___y_1285_ = v___y_1290_;
v___y_1286_ = v___x_1299_;
goto v___jp_1283_;
}
}
else
{
size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = ((size_t)0ULL);
v___x_1301_ = lean_usize_of_nat(v___x_1294_);
v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1291_, v___x_1300_, v___x_1301_, v___y_1289_);
lean_dec_ref(v_buckets_1291_);
v___y_1284_ = v___y_1292_;
v___y_1285_ = v___y_1290_;
v___y_1286_ = v___x_1302_;
goto v___jp_1283_;
}
}
}
v___jp_1303_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_array_get_size(v_buckets_1307_);
v___x_1310_ = lean_nat_dec_lt(v___x_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
v___y_1289_ = v___y_1304_;
v___y_1290_ = v___y_1306_;
v_buckets_1291_ = v_buckets_1307_;
v___y_1292_ = v___y_1305_;
goto v___jp_1288_;
}
else
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_nat_dec_le(v___x_1309_, v___x_1309_);
if (v___x_1311_ == 0)
{
if (v___x_1310_ == 0)
{
v___y_1289_ = v___y_1304_;
v___y_1290_ = v___y_1306_;
v_buckets_1291_ = v_buckets_1307_;
v___y_1292_ = v___y_1305_;
goto v___jp_1288_;
}
else
{
size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = lean_usize_of_nat(v___x_1309_);
v___x_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1307_, v___x_1312_, v___x_1313_, v___y_1305_);
v___y_1289_ = v___y_1304_;
v___y_1290_ = v___y_1306_;
v_buckets_1291_ = v_buckets_1307_;
v___y_1292_ = v___x_1314_;
goto v___jp_1288_;
}
}
else
{
size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = lean_usize_of_nat(v___x_1309_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1307_, v___x_1315_, v___x_1316_, v___y_1305_);
v___y_1289_ = v___y_1304_;
v___y_1290_ = v___y_1306_;
v_buckets_1291_ = v_buckets_1307_;
v___y_1292_ = v___x_1317_;
goto v___jp_1288_;
}
}
}
v___jp_1318_:
{
lean_object* v_buckets_1322_; 
v_buckets_1322_ = lean_ctor_get(v___y_1321_, 1);
lean_inc_ref(v_buckets_1322_);
v___y_1304_ = v___y_1319_;
v___y_1305_ = v___y_1320_;
v___y_1306_ = v___y_1321_;
v_buckets_1307_ = v_buckets_1322_;
goto v___jp_1303_;
}
v___jp_1323_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1329_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1330_ = lean_array_get_size(v_buckets_1325_);
v___x_1331_ = lean_nat_dec_lt(v___x_1327_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_dec_ref(v_buckets_1325_);
v___y_1304_ = v_snd_1326_;
v___y_1305_ = v_fst_1324_;
v___y_1306_ = v___x_1329_;
v_buckets_1307_ = v___x_1328_;
goto v___jp_1303_;
}
else
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_nat_dec_le(v___x_1330_, v___x_1330_);
if (v___x_1332_ == 0)
{
if (v___x_1331_ == 0)
{
lean_dec_ref(v_buckets_1325_);
v___y_1304_ = v_snd_1326_;
v___y_1305_ = v_fst_1324_;
v___y_1306_ = v___x_1329_;
v_buckets_1307_ = v___x_1328_;
goto v___jp_1303_;
}
else
{
size_t v___x_1333_; size_t v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = ((size_t)0ULL);
v___x_1334_ = lean_usize_of_nat(v___x_1330_);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(v_snd_1326_, v_buckets_1325_, v___x_1333_, v___x_1334_, v___x_1329_);
lean_dec_ref(v_buckets_1325_);
v___y_1319_ = v_snd_1326_;
v___y_1320_ = v_fst_1324_;
v___y_1321_ = v___x_1335_;
goto v___jp_1318_;
}
}
else
{
size_t v___x_1336_; size_t v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = lean_usize_of_nat(v___x_1330_);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__6(v_snd_1326_, v_buckets_1325_, v___x_1336_, v___x_1337_, v___x_1329_);
lean_dec_ref(v_buckets_1325_);
v___y_1319_ = v_snd_1326_;
v___y_1320_ = v_fst_1324_;
v___y_1321_ = v___x_1338_;
goto v___jp_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1340_, lean_object* v_y_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_x_1340_, v_y_1341_, v_a_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute(lean_object* v_x_1345_, lean_object* v_y_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_x_1345_, v_y_1346_, v_a_1347_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1354_, lean_object* v_y_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute(v_x_1354_, v_y_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1363_, lean_object* v_m_1364_, lean_object* v_a_1365_, lean_object* v_b_1366_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1364_, v_a_1365_, v_b_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1368_, lean_object* v_m_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1369_, v_a_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1372_, lean_object* v_m_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1372_, v_m_1373_, v_a_1374_);
lean_dec(v_a_1374_);
lean_dec_ref(v_m_1373_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1376_, lean_object* v_a_1377_, lean_object* v_b_1378_, lean_object* v_x_1379_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1377_, v_b_1378_, v_x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1381_, lean_object* v_a_1382_, lean_object* v_x_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1382_, v_x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1385_, lean_object* v_a_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1385_, v_a_1386_, v_x_1387_);
lean_dec(v_x_1387_);
lean_dec(v_a_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1389_, lean_object* v_x2_1390_){
_start:
{
lean_object* v_fst_1391_; lean_object* v_fst_1392_; uint8_t v___x_1393_; 
v_fst_1391_ = lean_ctor_get(v_x1_1389_, 0);
v_fst_1392_ = lean_ctor_get(v_x2_1390_, 0);
v___x_1393_ = lean_nat_dec_lt(v_fst_1391_, v_fst_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1394_, lean_object* v_x2_1395_){
_start:
{
uint8_t v_res_1396_; lean_object* v_r_1397_; 
v_res_1396_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1394_, v_x2_1395_);
lean_dec_ref(v_x2_1395_);
lean_dec_ref(v_x1_1394_);
v_r_1397_ = lean_box(v_res_1396_);
return v_r_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_as_1399_, lean_object* v_lo_1400_, lean_object* v_hi_1401_){
_start:
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_nat_dec_lt(v_lo_1400_, v_hi_1401_);
if (v___x_1402_ == 0)
{
lean_dec(v_lo_1400_);
return v_as_1399_;
}
else
{
lean_object* v___f_1403_; lean_object* v___x_1404_; lean_object* v_fst_1405_; lean_object* v_snd_1406_; uint8_t v___x_1407_; 
v___f_1403_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___closed__0));
lean_inc(v_lo_1400_);
v___x_1404_ = l_Array_qpartition___redArg(v_as_1399_, v___f_1403_, v_lo_1400_, v_hi_1401_);
v_fst_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_fst_1405_);
v_snd_1406_ = lean_ctor_get(v___x_1404_, 1);
lean_inc(v_snd_1406_);
lean_dec_ref(v___x_1404_);
v___x_1407_ = lean_nat_dec_le(v_hi_1401_, v_fst_1405_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_snd_1406_, v_lo_1400_, v_fst_1405_);
v___x_1409_ = lean_unsigned_to_nat(1u);
v___x_1410_ = lean_nat_add(v_fst_1405_, v___x_1409_);
lean_dec(v_fst_1405_);
v_as_1399_ = v___x_1408_;
v_lo_1400_ = v___x_1410_;
goto _start;
}
else
{
lean_dec(v_fst_1405_);
lean_dec(v_lo_1400_);
return v_snd_1406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_as_1412_, lean_object* v_lo_1413_, lean_object* v_hi_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_as_1412_, v_lo_1413_, v_hi_1414_);
lean_dec(v_hi_1414_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1416_, lean_object* v___x_1417_, lean_object* v_op_1418_, lean_object* v_a_1419_, lean_object* v_b_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___y_1424_; uint8_t v___x_1428_; 
v___x_1428_ = lean_nat_dec_lt(v_a_1419_, v_upperBound_1416_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec(v_a_1419_);
lean_dec_ref(v_op_1418_);
lean_dec_ref(v___x_1417_);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v_b_1420_);
lean_ctor_set(v___x_1429_, 1, v___y_1421_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
else
{
if (lean_obj_tag(v_b_1420_) == 0)
{
lean_object* v___x_1431_; 
lean_inc_ref(v___x_1417_);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1417_);
v___y_1424_ = v___x_1431_;
goto v___jp_1423_;
}
else
{
lean_object* v_val_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1441_; 
v_val_1432_ = lean_ctor_get(v_b_1420_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_b_1420_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1434_ = v_b_1420_;
v_isShared_1435_ = v_isSharedCheck_1441_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_val_1432_);
lean_dec(v_b_1420_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1441_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
lean_inc_ref(v_op_1418_);
v___x_1436_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_op_1418_);
lean_inc_ref(v___x_1417_);
v___x_1437_ = l_Lean_mkAppB(v___x_1436_, v_val_1432_, v___x_1417_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1437_);
v___x_1439_ = v___x_1434_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
v___y_1424_ = v___x_1439_;
goto v___jp_1423_;
}
}
}
}
v___jp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = lean_nat_add(v_a_1419_, v___x_1425_);
lean_dec(v_a_1419_);
v_a_1419_ = v___x_1426_;
v_b_1420_ = v___y_1424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1442_, lean_object* v___x_1443_, lean_object* v_op_1444_, lean_object* v_a_1445_, lean_object* v_b_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1442_, v___x_1443_, v_op_1444_, v_a_1445_, v_b_1446_, v___y_1447_);
lean_dec(v_upperBound_1442_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1450_, lean_object* v_as_1451_, size_t v_sz_1452_, size_t v_i_1453_, lean_object* v_b_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_usize_dec_lt(v_i_1453_, v_sz_1452_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec_ref(v_op_1450_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_b_1454_);
lean_ctor_set(v___x_1462_, 1, v___y_1455_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
return v___x_1463_;
}
else
{
lean_object* v_a_1464_; lean_object* v_fst_1465_; lean_object* v_snd_1466_; lean_object* v_varToExpr_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_a_1464_ = lean_array_uget_borrowed(v_as_1451_, v_i_1453_);
v_fst_1465_ = lean_ctor_get(v_a_1464_, 0);
v_snd_1466_ = lean_ctor_get(v_a_1464_, 1);
v_varToExpr_1467_ = lean_ctor_get(v___y_1455_, 2);
v___x_1468_ = l_Lean_instInhabitedExpr;
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = lean_array_get(v___x_1468_, v_varToExpr_1467_, v_fst_1465_);
lean_inc_ref(v_op_1450_);
v___x_1471_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1466_, v___x_1470_, v_op_1450_, v___x_1469_, v_b_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v_fst_1473_; lean_object* v_snd_1474_; size_t v___x_1475_; size_t v___x_1476_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1471_);
v_fst_1473_ = lean_ctor_get(v_a_1472_, 0);
lean_inc(v_fst_1473_);
v_snd_1474_ = lean_ctor_get(v_a_1472_, 1);
lean_inc(v_snd_1474_);
lean_dec(v_a_1472_);
v___x_1475_ = ((size_t)1ULL);
v___x_1476_ = lean_usize_add(v_i_1453_, v___x_1475_);
v_i_1453_ = v___x_1476_;
v_b_1454_ = v_fst_1473_;
v___y_1455_ = v_snd_1474_;
goto _start;
}
else
{
lean_dec_ref(v_op_1450_);
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1478_, lean_object* v_as_1479_, lean_object* v_sz_1480_, lean_object* v_i_1481_, lean_object* v_b_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
size_t v_sz_boxed_1489_; size_t v_i_boxed_1490_; lean_object* v_res_1491_; 
v_sz_boxed_1489_ = lean_unbox_usize(v_sz_1480_);
lean_dec(v_sz_1480_);
v_i_boxed_1490_ = lean_unbox_usize(v_i_1481_);
lean_dec(v_i_1481_);
v_res_1491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1478_, v_as_1479_, v_sz_boxed_1489_, v_i_boxed_1490_, v_b_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec_ref(v_as_1479_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1492_, lean_object* v_x_1493_){
_start:
{
if (lean_obj_tag(v_x_1493_) == 0)
{
return v_x_1492_;
}
else
{
lean_object* v_key_1494_; lean_object* v_value_1495_; lean_object* v_tail_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_key_1494_ = lean_ctor_get(v_x_1493_, 0);
v_value_1495_ = lean_ctor_get(v_x_1493_, 1);
v_tail_1496_ = lean_ctor_get(v_x_1493_, 2);
lean_inc(v_value_1495_);
lean_inc(v_key_1494_);
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v_key_1494_);
lean_ctor_set(v___x_1497_, 1, v_value_1495_);
v___x_1498_ = lean_array_push(v_x_1492_, v___x_1497_);
v_x_1492_ = v___x_1498_;
v_x_1493_ = v_tail_1496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1500_, v_x_1501_);
lean_dec(v_x_1501_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1503_, size_t v_i_1504_, size_t v_stop_1505_, lean_object* v_b_1506_){
_start:
{
uint8_t v___x_1507_; 
v___x_1507_ = lean_usize_dec_eq(v_i_1504_, v_stop_1505_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; size_t v___x_1510_; size_t v___x_1511_; 
v___x_1508_ = lean_array_uget_borrowed(v_as_1503_, v_i_1504_);
v___x_1509_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1506_, v___x_1508_);
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_add(v_i_1504_, v___x_1510_);
v_i_1504_ = v___x_1511_;
v_b_1506_ = v___x_1509_;
goto _start;
}
else
{
return v_b_1506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1513_, lean_object* v_i_1514_, lean_object* v_stop_1515_, lean_object* v_b_1516_){
_start:
{
size_t v_i_boxed_1517_; size_t v_stop_boxed_1518_; lean_object* v_res_1519_; 
v_i_boxed_1517_ = lean_unbox_usize(v_i_1514_);
lean_dec(v_i_1514_);
v_stop_boxed_1518_ = lean_unbox_usize(v_stop_1515_);
lean_dec(v_stop_1515_);
v_res_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1513_, v_i_boxed_1517_, v_stop_boxed_1518_, v_b_1516_);
lean_dec_ref(v_as_1513_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1520_, lean_object* v_op_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___y_1529_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1547_; lean_object* v_size_1554_; lean_object* v_buckets_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_size_1554_ = lean_ctor_get(v_coeff_1520_, 0);
v_buckets_1555_ = lean_ctor_get(v_coeff_1520_, 1);
v___x_1556_ = lean_mk_empty_array_with_capacity(v_size_1554_);
v___x_1557_ = lean_unsigned_to_nat(0u);
v___x_1558_ = lean_array_get_size(v_buckets_1555_);
v___x_1559_ = lean_nat_dec_lt(v___x_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
v___y_1547_ = v___x_1556_;
goto v___jp_1546_;
}
else
{
uint8_t v___x_1560_; 
v___x_1560_ = lean_nat_dec_le(v___x_1558_, v___x_1558_);
if (v___x_1560_ == 0)
{
if (v___x_1559_ == 0)
{
v___y_1547_ = v___x_1556_;
goto v___jp_1546_;
}
else
{
size_t v___x_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = ((size_t)0ULL);
v___x_1562_ = lean_usize_of_nat(v___x_1558_);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1555_, v___x_1561_, v___x_1562_, v___x_1556_);
v___y_1547_ = v___x_1563_;
goto v___jp_1546_;
}
}
else
{
size_t v___x_1564_; size_t v___x_1565_; lean_object* v___x_1566_; 
v___x_1564_ = ((size_t)0ULL);
v___x_1565_ = lean_usize_of_nat(v___x_1558_);
v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1555_, v___x_1564_, v___x_1565_, v___x_1556_);
v___y_1547_ = v___x_1566_;
goto v___jp_1546_;
}
}
v___jp_1528_:
{
lean_object* v_acc_1530_; size_t v_sz_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
v_acc_1530_ = lean_box(0);
v_sz_1531_ = lean_array_size(v___y_1529_);
v___x_1532_ = ((size_t)0ULL);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1521_, v___y_1529_, v_sz_1531_, v___x_1532_, v_acc_1530_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
lean_dec_ref(v___y_1529_);
return v___x_1533_;
}
v___jp_1534_:
{
lean_object* v___x_1539_; 
lean_dec(v___y_1535_);
v___x_1539_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
v___y_1529_ = v___x_1539_;
goto v___jp_1528_;
}
v___jp_1540_:
{
uint8_t v___x_1545_; 
v___x_1545_ = lean_nat_dec_le(v___y_1544_, v___y_1543_);
if (v___x_1545_ == 0)
{
lean_dec(v___y_1543_);
lean_inc(v___y_1544_);
v___y_1535_ = v___y_1541_;
v___y_1536_ = v___y_1542_;
v___y_1537_ = v___y_1544_;
v___y_1538_ = v___y_1544_;
goto v___jp_1534_;
}
else
{
v___y_1535_ = v___y_1541_;
v___y_1536_ = v___y_1542_;
v___y_1537_ = v___y_1544_;
v___y_1538_ = v___y_1543_;
goto v___jp_1534_;
}
}
v___jp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1548_ = lean_array_get_size(v___y_1547_);
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = lean_nat_dec_eq(v___x_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1551_ = lean_unsigned_to_nat(1u);
v___x_1552_ = lean_nat_sub(v___x_1548_, v___x_1551_);
v___x_1553_ = lean_nat_dec_le(v___x_1549_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_inc(v___x_1552_);
v___y_1541_ = v___x_1548_;
v___y_1542_ = v___y_1547_;
v___y_1543_ = v___x_1552_;
v___y_1544_ = v___x_1552_;
goto v___jp_1540_;
}
else
{
v___y_1541_ = v___x_1548_;
v___y_1542_ = v___y_1547_;
v___y_1543_ = v___x_1552_;
v___y_1544_ = v___x_1549_;
goto v___jp_1540_;
}
}
else
{
v___y_1529_ = v___y_1547_;
goto v___jp_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1567_, lean_object* v_op_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_coeff_1567_, v_op_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec_ref(v_coeff_1567_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1576_, lean_object* v___x_1577_, lean_object* v_op_1578_, lean_object* v_inst_1579_, lean_object* v_R_1580_, lean_object* v_a_1581_, lean_object* v_b_1582_, lean_object* v_c_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1576_, v___x_1577_, v_op_1578_, v_a_1581_, v_b_1582_, v___y_1584_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1591_, lean_object* v___x_1592_, lean_object* v_op_1593_, lean_object* v_inst_1594_, lean_object* v_R_1595_, lean_object* v_a_1596_, lean_object* v_b_1597_, lean_object* v_c_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1591_, v___x_1592_, v_op_1593_, v_inst_1594_, v_R_1595_, v_a_1596_, v_b_1597_, v_c_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v_upperBound_1591_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1606_, lean_object* v_as_1607_, lean_object* v_lo_1608_, lean_object* v_hi_1609_, lean_object* v_w_1610_, lean_object* v_hlo_1611_, lean_object* v_hhi_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_as_1607_, v_lo_1608_, v_hi_1609_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1614_, lean_object* v_as_1615_, lean_object* v_lo_1616_, lean_object* v_hi_1617_, lean_object* v_w_1618_, lean_object* v_hlo_1619_, lean_object* v_hhi_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1614_, v_as_1615_, v_lo_1616_, v_hi_1617_, v_w_1618_, v_hlo_1619_, v_hhi_1620_);
lean_dec(v_hi_1617_);
lean_dec(v_n_1614_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v___x_1625_; 
v___x_1625_ = l_Lean_Expr_hasMVar(v_e_1622_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v_e_1622_);
return v___x_1626_;
}
else
{
lean_object* v___x_1627_; lean_object* v_mctx_1628_; lean_object* v___x_1629_; lean_object* v_fst_1630_; lean_object* v_snd_1631_; lean_object* v___x_1632_; lean_object* v_cache_1633_; lean_object* v_zetaDeltaFVarIds_1634_; lean_object* v_postponed_1635_; lean_object* v_diag_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1645_; 
v___x_1627_ = lean_st_ref_get(v___y_1623_);
v_mctx_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc_ref(v_mctx_1628_);
lean_dec(v___x_1627_);
v___x_1629_ = l_Lean_instantiateMVarsCore(v_mctx_1628_, v_e_1622_);
v_fst_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_fst_1630_);
v_snd_1631_ = lean_ctor_get(v___x_1629_, 1);
lean_inc(v_snd_1631_);
lean_dec_ref(v___x_1629_);
v___x_1632_ = lean_st_ref_take(v___y_1623_);
v_cache_1633_ = lean_ctor_get(v___x_1632_, 1);
v_zetaDeltaFVarIds_1634_ = lean_ctor_get(v___x_1632_, 2);
v_postponed_1635_ = lean_ctor_get(v___x_1632_, 3);
v_diag_1636_ = lean_ctor_get(v___x_1632_, 4);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v___x_1632_, 0);
lean_dec(v_unused_1646_);
v___x_1638_ = v___x_1632_;
v_isShared_1639_ = v_isSharedCheck_1645_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_diag_1636_);
lean_inc(v_postponed_1635_);
lean_inc(v_zetaDeltaFVarIds_1634_);
lean_inc(v_cache_1633_);
lean_dec(v___x_1632_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1645_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v_snd_1631_);
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_snd_1631_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_cache_1633_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_zetaDeltaFVarIds_1634_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_postponed_1635_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_diag_1636_);
v___x_1641_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_st_ref_set(v___y_1623_, v___x_1641_);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v_fst_1630_);
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1647_, v___y_1648_);
lean_dec(v___y_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1651_, v___y_1653_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0(v_e_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(lean_object* v_x_1665_, lean_object* v_y_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v___x_1672_; 
lean_inc(v_a_1670_);
lean_inc_ref(v_a_1669_);
lean_inc(v_a_1668_);
lean_inc_ref(v_a_1667_);
v___x_1672_ = l_Lean_Meta_mkEq(v_x_1665_, v_y_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1695_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1695_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1695_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set_tag(v___x_1675_, 1);
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
uint8_t v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = 0;
v___x_1680_ = lean_box(0);
lean_inc_ref(v_a_1667_);
v___x_1681_ = l_Lean_Meta_mkFreshExprMVar(v___x_1678_, v___x_1679_, v___x_1680_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref(v___x_1681_);
v___x_1683_ = l_Lean_Expr_mvarId_x21(v_a_1682_);
lean_inc(v_a_1668_);
v___x_1684_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1683_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v___x_1685_; 
lean_dec_ref(v___x_1684_);
v___x_1685_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1682_, v_a_1668_);
lean_dec(v_a_1668_);
return v___x_1685_;
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_a_1682_);
lean_dec(v_a_1668_);
v_a_1686_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1684_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1684_);
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
else
{
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
return v___x_1681_;
}
}
}
}
else
{
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1696_, lean_object* v_y_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(v_x_1696_, v_y_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_options_1707_; uint8_t v_hasTrace_1708_; 
v_options_1707_ = lean_ctor_get(v___y_1705_, 2);
v_hasTrace_1708_ = lean_ctor_get_uint8(v_options_1707_, sizeof(void*)*1);
if (v_hasTrace_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec(v_cls_1704_);
v___x_1709_ = lean_box(v_hasTrace_1708_);
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
return v___x_1710_;
}
else
{
lean_object* v_inheritedTraceOptions_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_inheritedTraceOptions_1711_ = lean_ctor_get(v___y_1705_, 13);
v___x_1712_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_1713_ = l_Lean_Name_append(v___x_1712_, v_cls_1704_);
v___x_1714_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1711_, v_options_1707_, v___x_1713_);
lean_dec(v___x_1713_);
v___x_1715_ = lean_box(v___x_1714_);
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_1717_, v___y_1718_);
lean_dec_ref(v___y_1718_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_1721_, v___y_1727_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0(v_cls_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
return v_res_1740_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = lean_unsigned_to_nat(32u);
v___x_1742_ = lean_mk_empty_array_with_capacity(v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
return v___x_1743_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1744_ = ((size_t)5ULL);
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = lean_unsigned_to_nat(32u);
v___x_1747_ = lean_mk_empty_array_with_capacity(v___x_1746_);
v___x_1748_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___closed__0);
v___x_1749_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
lean_ctor_set(v___x_1749_, 1, v___x_1747_);
lean_ctor_set(v___x_1749_, 2, v___x_1745_);
lean_ctor_set(v___x_1749_, 3, v___x_1745_);
lean_ctor_set_usize(v___x_1749_, 4, v___x_1744_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg(lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; lean_object* v_traceState_1753_; lean_object* v_traces_1754_; lean_object* v___x_1755_; lean_object* v_traceState_1756_; lean_object* v_env_1757_; lean_object* v_nextMacroScope_1758_; lean_object* v_ngen_1759_; lean_object* v_auxDeclNGen_1760_; lean_object* v_cache_1761_; lean_object* v_messages_1762_; lean_object* v_infoState_1763_; lean_object* v_snapshotTasks_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1783_; 
v___x_1752_ = lean_st_ref_get(v___y_1750_);
v_traceState_1753_ = lean_ctor_get(v___x_1752_, 4);
lean_inc_ref(v_traceState_1753_);
lean_dec(v___x_1752_);
v_traces_1754_ = lean_ctor_get(v_traceState_1753_, 0);
lean_inc_ref(v_traces_1754_);
lean_dec_ref(v_traceState_1753_);
v___x_1755_ = lean_st_ref_take(v___y_1750_);
v_traceState_1756_ = lean_ctor_get(v___x_1755_, 4);
v_env_1757_ = lean_ctor_get(v___x_1755_, 0);
v_nextMacroScope_1758_ = lean_ctor_get(v___x_1755_, 1);
v_ngen_1759_ = lean_ctor_get(v___x_1755_, 2);
v_auxDeclNGen_1760_ = lean_ctor_get(v___x_1755_, 3);
v_cache_1761_ = lean_ctor_get(v___x_1755_, 5);
v_messages_1762_ = lean_ctor_get(v___x_1755_, 6);
v_infoState_1763_ = lean_ctor_get(v___x_1755_, 7);
v_snapshotTasks_1764_ = lean_ctor_get(v___x_1755_, 8);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1766_ = v___x_1755_;
v_isShared_1767_ = v_isSharedCheck_1783_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_snapshotTasks_1764_);
lean_inc(v_infoState_1763_);
lean_inc(v_messages_1762_);
lean_inc(v_cache_1761_);
lean_inc(v_traceState_1756_);
lean_inc(v_auxDeclNGen_1760_);
lean_inc(v_ngen_1759_);
lean_inc(v_nextMacroScope_1758_);
lean_inc(v_env_1757_);
lean_dec(v___x_1755_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1783_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
uint64_t v_tid_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1781_; 
v_tid_1768_ = lean_ctor_get_uint64(v_traceState_1756_, sizeof(void*)*1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_traceState_1756_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; 
v_unused_1782_ = lean_ctor_get(v_traceState_1756_, 0);
lean_dec(v_unused_1782_);
v___x_1770_ = v_traceState_1756_;
v_isShared_1771_ = v_isSharedCheck_1781_;
goto v_resetjp_1769_;
}
else
{
lean_dec(v_traceState_1756_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1781_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___closed__1);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1772_);
v___x_1774_ = v___x_1770_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1772_);
lean_ctor_set_uint64(v_reuseFailAlloc_1780_, sizeof(void*)*1, v_tid_1768_);
v___x_1774_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1776_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 4, v___x_1774_);
v___x_1776_ = v___x_1766_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_env_1757_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_nextMacroScope_1758_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_ngen_1759_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_auxDeclNGen_1760_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1779_, 5, v_cache_1761_);
lean_ctor_set(v_reuseFailAlloc_1779_, 6, v_messages_1762_);
lean_ctor_set(v_reuseFailAlloc_1779_, 7, v_infoState_1763_);
lean_ctor_set(v_reuseFailAlloc_1779_, 8, v_snapshotTasks_1764_);
v___x_1776_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_st_ref_set(v___y_1750_, v___x_1776_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_traces_1754_);
return v___x_1778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg___boxed(lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg(v___y_1784_);
lean_dec(v___y_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg(v___y_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2(v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
return v_res_1804_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_opts_1805_, lean_object* v_opt_1806_){
_start:
{
lean_object* v_name_1807_; lean_object* v_defValue_1808_; lean_object* v_map_1809_; lean_object* v___x_1810_; 
v_name_1807_ = lean_ctor_get(v_opt_1806_, 0);
v_defValue_1808_ = lean_ctor_get(v_opt_1806_, 1);
v_map_1809_ = lean_ctor_get(v_opts_1805_, 0);
v___x_1810_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1809_, v_name_1807_);
if (lean_obj_tag(v___x_1810_) == 0)
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_unbox(v_defValue_1808_);
return v___x_1811_;
}
else
{
lean_object* v_val_1812_; 
v_val_1812_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_val_1812_);
lean_dec_ref(v___x_1810_);
if (lean_obj_tag(v_val_1812_) == 1)
{
uint8_t v_v_1813_; 
v_v_1813_ = lean_ctor_get_uint8(v_val_1812_, 0);
lean_dec_ref(v_val_1812_);
return v_v_1813_;
}
else
{
uint8_t v___x_1814_; 
lean_dec(v_val_1812_);
v___x_1814_ = lean_unbox(v_defValue_1808_);
return v___x_1814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object* v_opts_1815_, lean_object* v_opt_1816_){
_start:
{
uint8_t v_res_1817_; lean_object* v_r_1818_; 
v_res_1817_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_opts_1815_, v_opt_1816_);
lean_dec_ref(v_opt_1816_);
lean_dec_ref(v_opts_1815_);
v_r_1818_ = lean_box(v_res_1817_);
return v_r_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0(lean_object* v___x_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_mkAppB(v___x_1819_, v___y_1820_, v___y_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1(lean_object* v_val_1823_, lean_object* v_lhs_1824_, lean_object* v_rhs_1825_, lean_object* v_P_1826_, uint8_t v___x_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; 
lean_inc_ref(v_lhs_1824_);
lean_inc_ref(v_val_1823_);
v___x_1834_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_1823_, v_lhs_1824_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v_fst_1836_; lean_object* v_snd_1837_; lean_object* v___x_1838_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref(v___x_1834_);
v_fst_1836_ = lean_ctor_get(v_a_1835_, 0);
lean_inc(v_fst_1836_);
v_snd_1837_ = lean_ctor_get(v_a_1835_, 1);
lean_inc(v_snd_1837_);
lean_dec(v_a_1835_);
lean_inc_ref(v_rhs_1825_);
lean_inc_ref(v_val_1823_);
v___x_1838_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_1823_, v_rhs_1825_, v_snd_1837_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v_fst_1840_; lean_object* v_snd_1841_; lean_object* v___x_1842_; lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1933_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref(v___x_1838_);
v_fst_1840_ = lean_ctor_get(v_a_1839_, 0);
lean_inc(v_fst_1840_);
v_snd_1841_ = lean_ctor_get(v_a_1839_, 1);
lean_inc(v_snd_1841_);
lean_dec(v_a_1839_);
v___x_1842_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_fst_1836_, v_fst_1840_, v_snd_1841_);
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1933_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1933_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v_fst_1847_; lean_object* v_snd_1848_; lean_object* v_common_1849_; lean_object* v_x_1850_; lean_object* v_y_1851_; lean_object* v___x_1852_; 
v_fst_1847_ = lean_ctor_get(v_a_1843_, 0);
lean_inc(v_fst_1847_);
v_snd_1848_ = lean_ctor_get(v_a_1843_, 1);
lean_inc(v_snd_1848_);
lean_dec(v_a_1843_);
v_common_1849_ = lean_ctor_get(v_fst_1847_, 0);
lean_inc_ref(v_common_1849_);
v_x_1850_ = lean_ctor_get(v_fst_1847_, 1);
lean_inc_ref(v_x_1850_);
v_y_1851_ = lean_ctor_get(v_fst_1847_, 2);
lean_inc_ref(v_y_1851_);
lean_dec(v_fst_1847_);
lean_inc_ref(v_val_1823_);
v___x_1852_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_common_1849_, v_val_1823_, v_snd_1848_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_common_1849_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v_fst_1854_; lean_object* v_snd_1855_; lean_object* v___x_1856_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref(v___x_1852_);
v_fst_1854_ = lean_ctor_get(v_a_1853_, 0);
lean_inc(v_fst_1854_);
v_snd_1855_ = lean_ctor_get(v_a_1853_, 1);
lean_inc(v_snd_1855_);
lean_dec(v_a_1853_);
lean_inc_ref(v_val_1823_);
v___x_1856_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_x_1850_, v_val_1823_, v_snd_1855_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_x_1850_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v_fst_1858_; lean_object* v_snd_1859_; lean_object* v___x_1860_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref(v___x_1856_);
v_fst_1858_ = lean_ctor_get(v_a_1857_, 0);
lean_inc(v_fst_1858_);
v_snd_1859_ = lean_ctor_get(v_a_1857_, 1);
lean_inc(v_snd_1859_);
lean_dec(v_a_1857_);
lean_inc_ref(v_val_1823_);
v___x_1860_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_y_1851_, v_val_1823_, v_snd_1859_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec_ref(v_y_1851_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v_fst_1862_; lean_object* v_snd_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1908_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref(v___x_1860_);
v_fst_1862_ = lean_ctor_get(v_a_1861_, 0);
v_snd_1863_ = lean_ctor_get(v_a_1861_, 1);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_a_1861_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1865_ = v_a_1861_;
v_isShared_1866_ = v_isSharedCheck_1908_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_snd_1863_);
lean_inc(v_fst_1862_);
lean_dec(v_a_1861_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1908_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___x_1898_; lean_object* v___f_1899_; lean_object* v___y_1901_; lean_object* v___x_1905_; 
lean_inc_ref(v_val_1823_);
v___x_1898_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_1823_);
v___f_1899_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0), 3, 1);
lean_closure_set(v___f_1899_, 0, v___x_1898_);
lean_inc(v_fst_1854_);
lean_inc_ref(v___f_1899_);
v___x_1905_ = l_Option_merge___redArg(v___f_1899_, v_fst_1854_, v_fst_1858_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v___x_1906_; 
lean_inc_ref(v_val_1823_);
v___x_1906_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_1823_);
v___y_1901_ = v___x_1906_;
goto v___jp_1900_;
}
else
{
lean_object* v_val_1907_; 
v_val_1907_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_val_1907_);
lean_dec_ref(v___x_1905_);
v___y_1901_ = v_val_1907_;
goto v___jp_1900_;
}
v___jp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_inc_ref(v_P_1826_);
v___x_1870_ = l_Lean_mkAppB(v_P_1826_, v_lhs_1824_, v_rhs_1825_);
v___x_1871_ = l_Lean_mkAppB(v_P_1826_, v___y_1868_, v___y_1869_);
lean_inc_ref(v___x_1871_);
v___x_1872_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(v___x_1870_, v___x_1871_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1889_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1889_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1889_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set_tag(v___x_1845_, 1);
lean_ctor_set(v___x_1845_, 0, v_a_1873_);
v___x_1878_ = v___x_1845_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1879_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1879_, 0, v___x_1871_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*2, v___x_1827_);
v___x_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
v___x_1881_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1881_);
v___x_1883_ = v___x_1865_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_snd_1863_);
v___x_1883_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1883_);
v___x_1885_ = v___x_1875_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec_ref(v___x_1871_);
lean_del_object(v___x_1865_);
lean_dec(v_snd_1863_);
lean_del_object(v___x_1845_);
v_a_1890_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1872_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1872_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
v___jp_1900_:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Option_merge___redArg(v___f_1899_, v_fst_1854_, v_fst_1862_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_1823_);
v___y_1868_ = v___y_1901_;
v___y_1869_ = v___x_1903_;
goto v___jp_1867_;
}
else
{
lean_object* v_val_1904_; 
lean_dec_ref(v_val_1823_);
v_val_1904_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_val_1904_);
lean_dec_ref(v___x_1902_);
v___y_1868_ = v___y_1901_;
v___y_1869_ = v_val_1904_;
goto v___jp_1867_;
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_fst_1858_);
lean_dec(v_fst_1854_);
lean_del_object(v___x_1845_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v_P_1826_);
lean_dec_ref(v_rhs_1825_);
lean_dec_ref(v_lhs_1824_);
lean_dec_ref(v_val_1823_);
v_a_1909_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1860_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1860_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_fst_1854_);
lean_dec_ref(v_y_1851_);
lean_del_object(v___x_1845_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v_P_1826_);
lean_dec_ref(v_rhs_1825_);
lean_dec_ref(v_lhs_1824_);
lean_dec_ref(v_val_1823_);
v_a_1917_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1856_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1856_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec_ref(v_y_1851_);
lean_dec_ref(v_x_1850_);
lean_del_object(v___x_1845_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v_P_1826_);
lean_dec_ref(v_rhs_1825_);
lean_dec_ref(v_lhs_1824_);
lean_dec_ref(v_val_1823_);
v_a_1925_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1852_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1852_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec(v_fst_1836_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v_P_1826_);
lean_dec_ref(v_rhs_1825_);
lean_dec_ref(v_lhs_1824_);
lean_dec_ref(v_val_1823_);
v_a_1934_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1838_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1838_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v_P_1826_);
lean_dec_ref(v_rhs_1825_);
lean_dec_ref(v_lhs_1824_);
lean_dec_ref(v_val_1823_);
v_a_1942_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1834_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1834_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1___boxed(lean_object* v_val_1950_, lean_object* v_lhs_1951_, lean_object* v_rhs_1952_, lean_object* v_P_1953_, lean_object* v___x_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
uint8_t v___x_92914__boxed_1961_; lean_object* v_res_1962_; 
v___x_92914__boxed_1961_ = lean_unbox(v___x_1954_);
v_res_1962_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1(v_val_1950_, v_lhs_1951_, v_rhs_1952_, v_P_1953_, v___x_92914__boxed_1961_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
return v_res_1962_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___closed__0));
v___x_1965_ = l_Lean_stringToMessageData(v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_x_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___closed__1);
v___x_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_x_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__2(v_x_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v_x_1977_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(lean_object* v_val_1987_, lean_object* v_lhs_1988_, lean_object* v_rhs_1989_, lean_object* v_P_1990_, uint8_t v_hasTrace_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
lean_inc_ref(v_lhs_1988_);
lean_inc_ref(v_val_1987_);
v___x_1998_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_1987_, v_lhs_1988_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v_fst_2000_; lean_object* v_snd_2001_; lean_object* v___x_2002_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref(v___x_1998_);
v_fst_2000_ = lean_ctor_get(v_a_1999_, 0);
lean_inc(v_fst_2000_);
v_snd_2001_ = lean_ctor_get(v_a_1999_, 1);
lean_inc(v_snd_2001_);
lean_dec(v_a_1999_);
lean_inc_ref(v_rhs_1989_);
lean_inc_ref(v_val_1987_);
v___x_2002_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients(v_val_1987_, v_rhs_1989_, v_snd_2001_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___x_2006_; lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2097_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref(v___x_2002_);
v_fst_2004_ = lean_ctor_get(v_a_2003_, 0);
lean_inc(v_fst_2004_);
v_snd_2005_ = lean_ctor_get(v_a_2003_, 1);
lean_inc(v_snd_2005_);
lean_dec(v_a_2003_);
v___x_2006_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_SharedCoefficients_compute___redArg(v_fst_2000_, v_fst_2004_, v_snd_2005_);
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2097_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2097_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_fst_2011_; lean_object* v_snd_2012_; lean_object* v_common_2013_; lean_object* v_x_2014_; lean_object* v_y_2015_; lean_object* v___x_2016_; 
v_fst_2011_ = lean_ctor_get(v_a_2007_, 0);
lean_inc(v_fst_2011_);
v_snd_2012_ = lean_ctor_get(v_a_2007_, 1);
lean_inc(v_snd_2012_);
lean_dec(v_a_2007_);
v_common_2013_ = lean_ctor_get(v_fst_2011_, 0);
lean_inc_ref(v_common_2013_);
v_x_2014_ = lean_ctor_get(v_fst_2011_, 1);
lean_inc_ref(v_x_2014_);
v_y_2015_ = lean_ctor_get(v_fst_2011_, 2);
lean_inc_ref(v_y_2015_);
lean_dec(v_fst_2011_);
lean_inc_ref(v_val_1987_);
v___x_2016_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_common_2013_, v_val_1987_, v_snd_2012_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec_ref(v_common_2013_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v_fst_2018_; lean_object* v_snd_2019_; lean_object* v___x_2020_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref(v___x_2016_);
v_fst_2018_ = lean_ctor_get(v_a_2017_, 0);
lean_inc(v_fst_2018_);
v_snd_2019_ = lean_ctor_get(v_a_2017_, 1);
lean_inc(v_snd_2019_);
lean_dec(v_a_2017_);
lean_inc_ref(v_val_1987_);
v___x_2020_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_x_2014_, v_val_1987_, v_snd_2019_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec_ref(v_x_2014_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v_fst_2022_; lean_object* v_snd_2023_; lean_object* v___x_2024_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref(v___x_2020_);
v_fst_2022_ = lean_ctor_get(v_a_2021_, 0);
lean_inc(v_fst_2022_);
v_snd_2023_ = lean_ctor_get(v_a_2021_, 1);
lean_inc(v_snd_2023_);
lean_dec(v_a_2021_);
lean_inc_ref(v_val_1987_);
v___x_2024_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_CoefficientsMap_toExpr(v_y_2015_, v_val_1987_, v_snd_2023_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec_ref(v_y_2015_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v_fst_2026_; lean_object* v_snd_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2072_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2024_);
v_fst_2026_ = lean_ctor_get(v_a_2025_, 0);
v_snd_2027_ = lean_ctor_get(v_a_2025_, 1);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_a_2025_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2029_ = v_a_2025_;
v_isShared_2030_ = v_isSharedCheck_2072_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_snd_2027_);
lean_inc(v_fst_2026_);
lean_dec(v_a_2025_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2072_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___x_2062_; lean_object* v___f_2063_; lean_object* v___y_2065_; lean_object* v___x_2069_; 
lean_inc_ref(v_val_1987_);
v___x_2062_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_1987_);
v___f_2063_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__0), 3, 1);
lean_closure_set(v___f_2063_, 0, v___x_2062_);
lean_inc(v_fst_2018_);
lean_inc_ref(v___f_2063_);
v___x_2069_ = l_Option_merge___redArg(v___f_2063_, v_fst_2018_, v_fst_2022_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v___x_2070_; 
lean_inc_ref(v_val_1987_);
v___x_2070_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_1987_);
v___y_2065_ = v___x_2070_;
goto v___jp_2064_;
}
else
{
lean_object* v_val_2071_; 
v_val_2071_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_val_2071_);
lean_dec_ref(v___x_2069_);
v___y_2065_ = v_val_2071_;
goto v___jp_2064_;
}
v___jp_2031_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_inc_ref(v_P_1990_);
v___x_2034_ = l_Lean_mkAppB(v_P_1990_, v_lhs_1988_, v_rhs_1989_);
v___x_2035_ = l_Lean_mkAppB(v_P_1990_, v___y_2032_, v___y_2033_);
lean_inc_ref(v___x_2035_);
v___x_2036_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC(v___x_2034_, v___x_2035_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2053_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2053_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2053_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set_tag(v___x_2009_, 1);
lean_ctor_set(v___x_2009_, 0, v_a_2037_);
v___x_2042_ = v___x_2009_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2043_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2043_, 0, v___x_2035_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*2, v_hasTrace_1991_);
v___x_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
v___x_2045_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2045_);
v___x_2047_ = v___x_2029_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_snd_2027_);
v___x_2047_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2049_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2047_);
v___x_2049_ = v___x_2039_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec_ref(v___x_2035_);
lean_del_object(v___x_2029_);
lean_dec(v_snd_2027_);
lean_del_object(v___x_2009_);
v_a_2054_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2036_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2036_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
v___jp_2064_:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Option_merge___redArg(v___f_2063_, v_fst_2018_, v_fst_2026_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_neutralElement(v_val_1987_);
v___y_2032_ = v___y_2065_;
v___y_2033_ = v___x_2067_;
goto v___jp_2031_;
}
else
{
lean_object* v_val_2068_; 
lean_dec_ref(v_val_1987_);
v_val_2068_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_val_2068_);
lean_dec_ref(v___x_2066_);
v___y_2032_ = v___y_2065_;
v___y_2033_ = v_val_2068_;
goto v___jp_2031_;
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_fst_2022_);
lean_dec(v_fst_2018_);
lean_del_object(v___x_2009_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v_P_1990_);
lean_dec_ref(v_rhs_1989_);
lean_dec_ref(v_lhs_1988_);
lean_dec_ref(v_val_1987_);
v_a_2073_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2024_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2024_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_fst_2018_);
lean_dec_ref(v_y_2015_);
lean_del_object(v___x_2009_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v_P_1990_);
lean_dec_ref(v_rhs_1989_);
lean_dec_ref(v_lhs_1988_);
lean_dec_ref(v_val_1987_);
v_a_2081_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2020_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2020_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_y_2015_);
lean_dec_ref(v_x_2014_);
lean_del_object(v___x_2009_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v_P_1990_);
lean_dec_ref(v_rhs_1989_);
lean_dec_ref(v_lhs_1988_);
lean_dec_ref(v_val_1987_);
v_a_2089_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2016_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2016_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v_fst_2000_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v_P_1990_);
lean_dec_ref(v_rhs_1989_);
lean_dec_ref(v_lhs_1988_);
lean_dec_ref(v_val_1987_);
v_a_2098_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2002_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2002_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v_P_1990_);
lean_dec_ref(v_rhs_1989_);
lean_dec_ref(v_lhs_1988_);
lean_dec_ref(v_val_1987_);
v_a_2106_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_1998_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_1998_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object* v_val_2114_, lean_object* v_lhs_2115_, lean_object* v_rhs_2116_, lean_object* v_P_2117_, lean_object* v_hasTrace_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v_hasTrace_boxed_2125_; lean_object* v_res_2126_; 
v_hasTrace_boxed_2125_ = lean_unbox(v_hasTrace_2118_);
v_res_2126_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4(v_val_2114_, v_lhs_2115_, v_rhs_2116_, v_P_2117_, v_hasTrace_boxed_2125_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v_cls_2127_, lean_object* v_msg_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_ref_2134_; lean_object* v___x_2135_; lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2180_; 
v_ref_2134_ = lean_ctor_get(v___y_2131_, 5);
v___x_2135_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2180_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2180_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v_traceState_2141_; lean_object* v_env_2142_; lean_object* v_nextMacroScope_2143_; lean_object* v_ngen_2144_; lean_object* v_auxDeclNGen_2145_; lean_object* v_cache_2146_; lean_object* v_messages_2147_; lean_object* v_infoState_2148_; lean_object* v_snapshotTasks_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2179_; 
v___x_2140_ = lean_st_ref_take(v___y_2132_);
v_traceState_2141_ = lean_ctor_get(v___x_2140_, 4);
v_env_2142_ = lean_ctor_get(v___x_2140_, 0);
v_nextMacroScope_2143_ = lean_ctor_get(v___x_2140_, 1);
v_ngen_2144_ = lean_ctor_get(v___x_2140_, 2);
v_auxDeclNGen_2145_ = lean_ctor_get(v___x_2140_, 3);
v_cache_2146_ = lean_ctor_get(v___x_2140_, 5);
v_messages_2147_ = lean_ctor_get(v___x_2140_, 6);
v_infoState_2148_ = lean_ctor_get(v___x_2140_, 7);
v_snapshotTasks_2149_ = lean_ctor_get(v___x_2140_, 8);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2151_ = v___x_2140_;
v_isShared_2152_ = v_isSharedCheck_2179_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_snapshotTasks_2149_);
lean_inc(v_infoState_2148_);
lean_inc(v_messages_2147_);
lean_inc(v_cache_2146_);
lean_inc(v_traceState_2141_);
lean_inc(v_auxDeclNGen_2145_);
lean_inc(v_ngen_2144_);
lean_inc(v_nextMacroScope_2143_);
lean_inc(v_env_2142_);
lean_dec(v___x_2140_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2179_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
uint64_t v_tid_2153_; lean_object* v_traces_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2178_; 
v_tid_2153_ = lean_ctor_get_uint64(v_traceState_2141_, sizeof(void*)*1);
v_traces_2154_ = lean_ctor_get(v_traceState_2141_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_traceState_2141_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2156_ = v_traceState_2141_;
v_isShared_2157_ = v_isSharedCheck_2178_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_traces_2154_);
lean_dec(v_traceState_2141_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2178_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; double v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2158_ = lean_box(0);
v___x_2159_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__0);
v___x_2160_ = 0;
v___x_2161_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__1));
v___x_2162_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2162_, 0, v_cls_2127_);
lean_ctor_set(v___x_2162_, 1, v___x_2158_);
lean_ctor_set(v___x_2162_, 2, v___x_2161_);
lean_ctor_set_float(v___x_2162_, sizeof(void*)*3, v___x_2159_);
lean_ctor_set_float(v___x_2162_, sizeof(void*)*3 + 8, v___x_2159_);
lean_ctor_set_uint8(v___x_2162_, sizeof(void*)*3 + 16, v___x_2160_);
v___x_2163_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__2));
v___x_2164_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v_a_2136_);
lean_ctor_set(v___x_2164_, 2, v___x_2163_);
lean_inc(v_ref_2134_);
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v_ref_2134_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_Lean_PersistentArray_push___redArg(v_traces_2154_, v___x_2165_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2166_);
v___x_2168_ = v___x_2156_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2166_);
lean_ctor_set_uint64(v_reuseFailAlloc_2177_, sizeof(void*)*1, v_tid_2153_);
v___x_2168_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 4, v___x_2168_);
v___x_2170_ = v___x_2151_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_env_2142_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_nextMacroScope_2143_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_ngen_2144_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v_auxDeclNGen_2145_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2176_, 5, v_cache_2146_);
lean_ctor_set(v_reuseFailAlloc_2176_, 6, v_messages_2147_);
lean_ctor_set(v_reuseFailAlloc_2176_, 7, v_infoState_2148_);
lean_ctor_set(v_reuseFailAlloc_2176_, 8, v_snapshotTasks_2149_);
v___x_2170_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2171_ = lean_st_ref_set(v___y_2132_, v___x_2170_);
v___x_2172_ = lean_box(0);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2172_);
v___x_2174_ = v___x_2138_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v_cls_2181_, lean_object* v_msg_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2181_, v_msg_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2188_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__2(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__1));
v___x_2193_ = l_Lean_stringToMessageData(v___x_2192_);
return v___x_2193_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__4(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__3));
v___x_2196_ = l_Lean_stringToMessageData(v___x_2195_);
return v___x_2196_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__6(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__5));
v___x_2199_ = l_Lean_stringToMessageData(v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__7(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = lean_box(0);
v___x_2201_ = lean_unsigned_to_nat(16u);
v___x_2202_ = lean_mk_array(v___x_2201_, v___x_2200_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__8(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__7);
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v___x_2203_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__11(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__10));
v___x_2210_ = l_Lean_stringToMessageData(v___x_2209_);
return v___x_2210_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__13(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__12));
v___x_2213_ = l_Lean_stringToMessageData(v___x_2212_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__14));
v___x_2216_ = l_Lean_stringToMessageData(v___x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_lhs_2217_, lean_object* v_rhs_2218_, lean_object* v_cls_2219_, uint8_t v___x_2220_, lean_object* v_P_2221_, uint8_t v_hasTrace_2222_, lean_object* v_____r_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2241_; 
lean_inc_ref(v_lhs_2217_);
v___x_2241_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_lhs_2217_);
if (lean_obj_tag(v___x_2241_) == 1)
{
lean_object* v_val_2242_; lean_object* v___x_2243_; 
v_val_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_val_2242_);
lean_dec_ref(v___x_2241_);
lean_inc_ref(v_rhs_2218_);
v___x_2243_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_rhs_2218_);
if (lean_obj_tag(v___x_2243_) == 1)
{
lean_object* v_val_2244_; uint8_t v___x_2274_; 
v_val_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_val_2244_);
lean_dec_ref(v___x_2243_);
v___x_2274_ = lean_expr_eqv(v_val_2242_, v_val_2244_);
if (v___x_2274_ == 0)
{
lean_dec_ref(v_P_2221_);
goto v___jp_2245_;
}
else
{
if (v___x_2220_ == 0)
{
lean_object* v___x_2275_; lean_object* v_a_2276_; lean_object* v___x_2277_; lean_object* v___f_2278_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; uint8_t v___x_2288_; 
lean_dec(v_val_2244_);
lean_inc(v_cls_2219_);
v___x_2275_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2219_, v___y_2229_);
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref(v___x_2275_);
v___x_2277_ = lean_box(v_hasTrace_2222_);
lean_inc(v_val_2242_);
v___f_2278_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__4___boxed), 11, 5);
lean_closure_set(v___f_2278_, 0, v_val_2242_);
lean_closure_set(v___f_2278_, 1, v_lhs_2217_);
lean_closure_set(v___f_2278_, 2, v_rhs_2218_);
lean_closure_set(v___f_2278_, 3, v_P_2221_);
lean_closure_set(v___f_2278_, 4, v___x_2277_);
v___x_2288_ = lean_unbox(v_a_2276_);
lean_dec(v_a_2276_);
if (v___x_2288_ == 0)
{
lean_dec(v_cls_2219_);
v___y_2280_ = v___y_2227_;
v___y_2281_ = v___y_2228_;
v___y_2282_ = v___y_2229_;
v___y_2283_ = v___y_2230_;
goto v___jp_2279_;
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2289_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__11);
lean_inc(v_val_2242_);
v___x_2290_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2242_);
v___x_2291_ = l_Lean_MessageData_ofExpr(v___x_2290_);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2289_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__13);
v___x_2294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2219_, v___x_2294_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_dec_ref(v___x_2295_);
v___y_2280_ = v___y_2227_;
v___y_2281_ = v___y_2228_;
v___y_2282_ = v___y_2229_;
v___y_2283_ = v___y_2230_;
goto v___jp_2279_;
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref(v___f_2278_);
lean_dec(v_val_2242_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2295_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
v___jp_2279_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2284_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__8);
v___x_2285_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__9));
v___x_2286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2286_, 0, v_val_2242_);
lean_ctor_set(v___x_2286_, 1, v___x_2284_);
lean_ctor_set(v___x_2286_, 2, v___x_2285_);
v___x_2287_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v___f_2278_, v___x_2286_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2287_;
}
}
else
{
lean_dec_ref(v_P_2221_);
goto v___jp_2245_;
}
}
v___jp_2245_:
{
lean_object* v___x_2246_; lean_object* v_a_2247_; uint8_t v___x_2248_; 
lean_inc(v_cls_2219_);
v___x_2246_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2219_, v___y_2229_);
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = lean_unbox(v_a_2247_);
lean_dec(v_a_2247_);
if (v___x_2248_ == 0)
{
lean_dec(v_val_2244_);
lean_dec(v_val_2242_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v_cls_2219_);
lean_dec_ref(v_rhs_2218_);
lean_dec_ref(v_lhs_2217_);
goto v___jp_2232_;
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2249_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__2);
v___x_2250_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2242_);
v___x_2251_ = l_Lean_MessageData_ofExpr(v___x_2250_);
v___x_2252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2249_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__4);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = l_Lean_indentExpr(v_lhs_2217_);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__6);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2244_);
v___x_2260_ = l_Lean_MessageData_ofExpr(v___x_2259_);
v___x_2261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2258_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
lean_ctor_set(v___x_2262_, 1, v___x_2253_);
v___x_2263_ = l_Lean_indentExpr(v_rhs_2218_);
v___x_2264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2219_, v___x_2264_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_dec_ref(v___x_2265_);
goto v___jp_2232_;
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
}
else
{
lean_object* v___x_2304_; lean_object* v_a_2305_; uint8_t v___x_2306_; 
lean_dec(v___x_2243_);
lean_dec(v_val_2242_);
lean_dec_ref(v_P_2221_);
lean_dec_ref(v_lhs_2217_);
lean_inc(v_cls_2219_);
v___x_2304_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2219_, v___y_2229_);
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref(v___x_2304_);
v___x_2306_ = lean_unbox(v_a_2305_);
lean_dec(v_a_2305_);
if (v___x_2306_ == 0)
{
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v_cls_2219_);
lean_dec_ref(v_rhs_2218_);
goto v___jp_2235_;
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2307_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15);
v___x_2308_ = l_Lean_indentExpr(v_rhs_2218_);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2219_, v___x_2309_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_dec_ref(v___x_2310_);
goto v___jp_2235_;
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
}
else
{
lean_object* v___x_2319_; lean_object* v_a_2320_; uint8_t v___x_2321_; 
lean_dec(v___x_2241_);
lean_dec_ref(v_P_2221_);
lean_dec_ref(v_rhs_2218_);
lean_inc(v_cls_2219_);
v___x_2319_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2219_, v___y_2229_);
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref(v___x_2319_);
v___x_2321_ = lean_unbox(v_a_2320_);
lean_dec(v_a_2320_);
if (v___x_2321_ == 0)
{
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v_cls_2219_);
lean_dec_ref(v_lhs_2217_);
goto v___jp_2238_;
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2322_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15);
v___x_2323_ = l_Lean_indentExpr(v_lhs_2217_);
v___x_2324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2219_, v___x_2324_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_dec_ref(v___x_2325_);
goto v___jp_2238_;
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
v___jp_2232_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
v___jp_2235_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
return v___x_2237_;
}
v___jp_2238_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_lhs_2334_, lean_object* v_rhs_2335_, lean_object* v_cls_2336_, lean_object* v___x_2337_, lean_object* v_P_2338_, lean_object* v_hasTrace_2339_, lean_object* v_____r_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
uint8_t v___x_93620__boxed_2349_; uint8_t v_hasTrace_boxed_2350_; lean_object* v_res_2351_; 
v___x_93620__boxed_2349_ = lean_unbox(v___x_2337_);
v_hasTrace_boxed_2350_ = lean_unbox(v_hasTrace_2339_);
v_res_2351_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(v_lhs_2334_, v_rhs_2335_, v_cls_2336_, v___x_93620__boxed_2349_, v_P_2338_, v_hasTrace_boxed_2350_, v_____r_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__7(lean_object* v_lhs_2352_, lean_object* v_rhs_2353_, lean_object* v_P_2354_, uint8_t v___x_2355_, lean_object* v_cls_2356_, lean_object* v_____r_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2375_; 
lean_inc_ref(v_lhs_2352_);
v___x_2375_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_lhs_2352_);
if (lean_obj_tag(v___x_2375_) == 1)
{
lean_object* v_val_2376_; lean_object* v___x_2377_; 
v_val_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_val_2376_);
lean_dec_ref(v___x_2375_);
lean_inc_ref(v_rhs_2353_);
v___x_2377_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_rhs_2353_);
if (lean_obj_tag(v___x_2377_) == 1)
{
lean_object* v_val_2378_; lean_object* v___x_2379_; lean_object* v___f_2380_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; uint8_t v___x_2409_; 
v_val_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_val_2378_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = lean_box(v___x_2355_);
lean_inc_ref(v_rhs_2353_);
lean_inc_ref(v_lhs_2352_);
lean_inc(v_val_2376_);
v___f_2380_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1___boxed), 11, 5);
lean_closure_set(v___f_2380_, 0, v_val_2376_);
lean_closure_set(v___f_2380_, 1, v_lhs_2352_);
lean_closure_set(v___f_2380_, 2, v_rhs_2353_);
lean_closure_set(v___f_2380_, 3, v_P_2354_);
lean_closure_set(v___f_2380_, 4, v___x_2379_);
v___x_2409_ = lean_expr_eqv(v_val_2376_, v_val_2378_);
if (v___x_2409_ == 0)
{
if (v___x_2355_ == 0)
{
lean_dec(v_val_2378_);
lean_dec_ref(v_rhs_2353_);
lean_dec_ref(v_lhs_2352_);
goto v___jp_2390_;
}
else
{
lean_object* v___x_2410_; lean_object* v_a_2411_; uint8_t v___x_2412_; 
lean_dec_ref(v___f_2380_);
lean_inc(v_cls_2356_);
v___x_2410_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2356_, v___y_2363_);
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref(v___x_2410_);
v___x_2412_ = lean_unbox(v_a_2411_);
lean_dec(v_a_2411_);
if (v___x_2412_ == 0)
{
lean_dec(v_val_2378_);
lean_dec(v_val_2376_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v_cls_2356_);
lean_dec_ref(v_rhs_2353_);
lean_dec_ref(v_lhs_2352_);
goto v___jp_2366_;
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2413_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__2);
v___x_2414_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2376_);
v___x_2415_ = l_Lean_MessageData_ofExpr(v___x_2414_);
v___x_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2413_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__4);
v___x_2418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = l_Lean_indentExpr(v_lhs_2352_);
v___x_2420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2418_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
v___x_2421_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__6);
v___x_2422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2420_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2378_);
v___x_2424_ = l_Lean_MessageData_ofExpr(v___x_2423_);
v___x_2425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2422_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
lean_ctor_set(v___x_2426_, 1, v___x_2417_);
v___x_2427_ = l_Lean_indentExpr(v_rhs_2353_);
v___x_2428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2426_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2356_, v___x_2428_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_dec_ref(v___x_2429_);
goto v___jp_2366_;
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2378_);
lean_dec_ref(v_rhs_2353_);
lean_dec_ref(v_lhs_2352_);
goto v___jp_2390_;
}
v___jp_2381_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2386_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__8);
v___x_2387_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__9));
v___x_2388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2388_, 0, v_val_2376_);
lean_ctor_set(v___x_2388_, 1, v___x_2386_);
lean_ctor_set(v___x_2388_, 2, v___x_2387_);
v___x_2389_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v___f_2380_, v___x_2388_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2389_;
}
v___jp_2390_:
{
lean_object* v___x_2391_; lean_object* v_a_2392_; uint8_t v___x_2393_; 
lean_inc(v_cls_2356_);
v___x_2391_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2356_, v___y_2363_);
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref(v___x_2391_);
v___x_2393_ = lean_unbox(v_a_2392_);
lean_dec(v_a_2392_);
if (v___x_2393_ == 0)
{
lean_dec(v_cls_2356_);
v___y_2382_ = v___y_2361_;
v___y_2383_ = v___y_2362_;
v___y_2384_ = v___y_2363_;
v___y_2385_ = v___y_2364_;
goto v___jp_2381_;
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2394_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__11);
lean_inc(v_val_2376_);
v___x_2395_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2376_);
v___x_2396_ = l_Lean_MessageData_ofExpr(v___x_2395_);
v___x_2397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2394_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__13);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2356_, v___x_2399_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_dec_ref(v___x_2400_);
v___y_2382_ = v___y_2361_;
v___y_2383_ = v___y_2362_;
v___y_2384_ = v___y_2363_;
v___y_2385_ = v___y_2364_;
goto v___jp_2381_;
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec_ref(v___f_2380_);
lean_dec(v_val_2376_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
}
else
{
lean_object* v___x_2438_; lean_object* v_a_2439_; uint8_t v___x_2440_; 
lean_dec(v___x_2377_);
lean_dec(v_val_2376_);
lean_dec_ref(v_P_2354_);
lean_dec_ref(v_lhs_2352_);
lean_inc(v_cls_2356_);
v___x_2438_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2356_, v___y_2363_);
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref(v___x_2438_);
v___x_2440_ = lean_unbox(v_a_2439_);
lean_dec(v_a_2439_);
if (v___x_2440_ == 0)
{
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v_cls_2356_);
lean_dec_ref(v_rhs_2353_);
goto v___jp_2369_;
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2441_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15);
v___x_2442_ = l_Lean_indentExpr(v_rhs_2353_);
v___x_2443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2356_, v___x_2443_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_dec_ref(v___x_2444_);
goto v___jp_2369_;
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
}
else
{
lean_object* v___x_2453_; lean_object* v_a_2454_; uint8_t v___x_2455_; 
lean_dec(v___x_2375_);
lean_dec_ref(v_P_2354_);
lean_dec_ref(v_rhs_2353_);
lean_inc(v_cls_2356_);
v___x_2453_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2356_, v___y_2363_);
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref(v___x_2453_);
v___x_2455_ = lean_unbox(v_a_2454_);
lean_dec(v_a_2454_);
if (v___x_2455_ == 0)
{
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v_cls_2356_);
lean_dec_ref(v_lhs_2352_);
goto v___jp_2372_;
}
else
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2456_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15);
v___x_2457_ = l_Lean_indentExpr(v_lhs_2352_);
v___x_2458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2356_, v___x_2458_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_dec_ref(v___x_2459_);
goto v___jp_2372_;
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
v___jp_2366_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
v___jp_2369_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
return v___x_2371_;
}
v___jp_2372_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__7___boxed(lean_object* v_lhs_2468_, lean_object* v_rhs_2469_, lean_object* v_P_2470_, lean_object* v___x_2471_, lean_object* v_cls_2472_, lean_object* v_____r_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
uint8_t v___x_93927__boxed_2482_; lean_object* v_res_2483_; 
v___x_93927__boxed_2482_ = lean_unbox(v___x_2471_);
v_res_2483_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__7(v_lhs_2468_, v_rhs_2469_, v_P_2470_, v___x_93927__boxed_2482_, v_cls_2472_, v_____r_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__7(lean_object* v_opts_2484_, lean_object* v_opt_2485_){
_start:
{
lean_object* v_name_2486_; lean_object* v_defValue_2487_; lean_object* v_map_2488_; lean_object* v___x_2489_; 
v_name_2486_ = lean_ctor_get(v_opt_2485_, 0);
v_defValue_2487_ = lean_ctor_get(v_opt_2485_, 1);
v_map_2488_ = lean_ctor_get(v_opts_2484_, 0);
v___x_2489_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2488_, v_name_2486_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_inc(v_defValue_2487_);
return v_defValue_2487_;
}
else
{
lean_object* v_val_2490_; 
v_val_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_val_2490_);
lean_dec_ref(v___x_2489_);
if (lean_obj_tag(v_val_2490_) == 3)
{
lean_object* v_v_2491_; 
v_v_2491_ = lean_ctor_get(v_val_2490_, 0);
lean_inc(v_v_2491_);
lean_dec_ref(v_val_2490_);
return v_v_2491_;
}
else
{
lean_dec(v_val_2490_);
lean_inc(v_defValue_2487_);
return v_defValue_2487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__7___boxed(lean_object* v_opts_2492_, lean_object* v_opt_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__7(v_opts_2492_, v_opt_2493_);
lean_dec_ref(v_opt_2493_);
lean_dec_ref(v_opts_2492_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5_spec__6(size_t v_sz_2495_, size_t v_i_2496_, lean_object* v_bs_2497_){
_start:
{
uint8_t v___x_2498_; 
v___x_2498_ = lean_usize_dec_lt(v_i_2496_, v_sz_2495_);
if (v___x_2498_ == 0)
{
return v_bs_2497_;
}
else
{
lean_object* v_v_2499_; lean_object* v_msg_2500_; lean_object* v___x_2501_; lean_object* v_bs_x27_2502_; size_t v___x_2503_; size_t v___x_2504_; lean_object* v___x_2505_; 
v_v_2499_ = lean_array_uget_borrowed(v_bs_2497_, v_i_2496_);
v_msg_2500_ = lean_ctor_get(v_v_2499_, 1);
lean_inc_ref(v_msg_2500_);
v___x_2501_ = lean_unsigned_to_nat(0u);
v_bs_x27_2502_ = lean_array_uset(v_bs_2497_, v_i_2496_, v___x_2501_);
v___x_2503_ = ((size_t)1ULL);
v___x_2504_ = lean_usize_add(v_i_2496_, v___x_2503_);
v___x_2505_ = lean_array_uset(v_bs_x27_2502_, v_i_2496_, v_msg_2500_);
v_i_2496_ = v___x_2504_;
v_bs_2497_ = v___x_2505_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_2507_, lean_object* v_i_2508_, lean_object* v_bs_2509_){
_start:
{
size_t v_sz_boxed_2510_; size_t v_i_boxed_2511_; lean_object* v_res_2512_; 
v_sz_boxed_2510_ = lean_unbox_usize(v_sz_2507_);
lean_dec(v_sz_2507_);
v_i_boxed_2511_ = lean_unbox_usize(v_i_2508_);
lean_dec(v_i_2508_);
v_res_2512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5_spec__6(v_sz_boxed_2510_, v_i_boxed_2511_, v_bs_2509_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5___redArg(lean_object* v_oldTraces_2513_, lean_object* v_data_2514_, lean_object* v_ref_2515_, lean_object* v_msg_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_fileName_2522_; lean_object* v_fileMap_2523_; lean_object* v_options_2524_; lean_object* v_currRecDepth_2525_; lean_object* v_maxRecDepth_2526_; lean_object* v_ref_2527_; lean_object* v_currNamespace_2528_; lean_object* v_openDecls_2529_; lean_object* v_initHeartbeats_2530_; lean_object* v_maxHeartbeats_2531_; lean_object* v_quotContext_2532_; lean_object* v_currMacroScope_2533_; uint8_t v_diag_2534_; lean_object* v_cancelTk_x3f_2535_; uint8_t v_suppressElabErrors_2536_; lean_object* v_inheritedTraceOptions_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2592_; 
v_fileName_2522_ = lean_ctor_get(v___y_2519_, 0);
v_fileMap_2523_ = lean_ctor_get(v___y_2519_, 1);
v_options_2524_ = lean_ctor_get(v___y_2519_, 2);
v_currRecDepth_2525_ = lean_ctor_get(v___y_2519_, 3);
v_maxRecDepth_2526_ = lean_ctor_get(v___y_2519_, 4);
v_ref_2527_ = lean_ctor_get(v___y_2519_, 5);
v_currNamespace_2528_ = lean_ctor_get(v___y_2519_, 6);
v_openDecls_2529_ = lean_ctor_get(v___y_2519_, 7);
v_initHeartbeats_2530_ = lean_ctor_get(v___y_2519_, 8);
v_maxHeartbeats_2531_ = lean_ctor_get(v___y_2519_, 9);
v_quotContext_2532_ = lean_ctor_get(v___y_2519_, 10);
v_currMacroScope_2533_ = lean_ctor_get(v___y_2519_, 11);
v_diag_2534_ = lean_ctor_get_uint8(v___y_2519_, sizeof(void*)*14);
v_cancelTk_x3f_2535_ = lean_ctor_get(v___y_2519_, 12);
v_suppressElabErrors_2536_ = lean_ctor_get_uint8(v___y_2519_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2537_ = lean_ctor_get(v___y_2519_, 13);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___y_2519_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2539_ = v___y_2519_;
v_isShared_2540_ = v_isSharedCheck_2592_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_inheritedTraceOptions_2537_);
lean_inc(v_cancelTk_x3f_2535_);
lean_inc(v_currMacroScope_2533_);
lean_inc(v_quotContext_2532_);
lean_inc(v_maxHeartbeats_2531_);
lean_inc(v_initHeartbeats_2530_);
lean_inc(v_openDecls_2529_);
lean_inc(v_currNamespace_2528_);
lean_inc(v_ref_2527_);
lean_inc(v_maxRecDepth_2526_);
lean_inc(v_currRecDepth_2525_);
lean_inc(v_options_2524_);
lean_inc(v_fileMap_2523_);
lean_inc(v_fileName_2522_);
lean_dec(v___y_2519_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2592_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v_traceState_2542_; lean_object* v_traces_2543_; lean_object* v_ref_2544_; lean_object* v___x_2546_; 
v___x_2541_ = lean_st_ref_get(v___y_2520_);
v_traceState_2542_ = lean_ctor_get(v___x_2541_, 4);
lean_inc_ref(v_traceState_2542_);
lean_dec(v___x_2541_);
v_traces_2543_ = lean_ctor_get(v_traceState_2542_, 0);
lean_inc_ref(v_traces_2543_);
lean_dec_ref(v_traceState_2542_);
v_ref_2544_ = l_Lean_replaceRef(v_ref_2515_, v_ref_2527_);
lean_dec(v_ref_2527_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 5, v_ref_2544_);
v___x_2546_ = v___x_2539_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_fileName_2522_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_fileMap_2523_);
lean_ctor_set(v_reuseFailAlloc_2591_, 2, v_options_2524_);
lean_ctor_set(v_reuseFailAlloc_2591_, 3, v_currRecDepth_2525_);
lean_ctor_set(v_reuseFailAlloc_2591_, 4, v_maxRecDepth_2526_);
lean_ctor_set(v_reuseFailAlloc_2591_, 5, v_ref_2544_);
lean_ctor_set(v_reuseFailAlloc_2591_, 6, v_currNamespace_2528_);
lean_ctor_set(v_reuseFailAlloc_2591_, 7, v_openDecls_2529_);
lean_ctor_set(v_reuseFailAlloc_2591_, 8, v_initHeartbeats_2530_);
lean_ctor_set(v_reuseFailAlloc_2591_, 9, v_maxHeartbeats_2531_);
lean_ctor_set(v_reuseFailAlloc_2591_, 10, v_quotContext_2532_);
lean_ctor_set(v_reuseFailAlloc_2591_, 11, v_currMacroScope_2533_);
lean_ctor_set(v_reuseFailAlloc_2591_, 12, v_cancelTk_x3f_2535_);
lean_ctor_set(v_reuseFailAlloc_2591_, 13, v_inheritedTraceOptions_2537_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, sizeof(void*)*14, v_diag_2534_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, sizeof(void*)*14 + 1, v_suppressElabErrors_2536_);
v___x_2546_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2547_; size_t v_sz_2548_; size_t v___x_2549_; lean_object* v___x_2550_; lean_object* v_msg_2551_; lean_object* v___x_2552_; lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2590_; 
v___x_2547_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2543_);
lean_dec_ref(v_traces_2543_);
v_sz_2548_ = lean_array_size(v___x_2547_);
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5_spec__6(v_sz_2548_, v___x_2549_, v___x_2547_);
v_msg_2551_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2551_, 0, v_data_2514_);
lean_ctor_set(v_msg_2551_, 1, v_msg_2516_);
lean_ctor_set(v_msg_2551_, 2, v___x_2550_);
v___x_2552_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2551_, v___y_2517_, v___y_2518_, v___x_2546_, v___y_2520_);
lean_dec_ref(v___x_2546_);
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2590_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2590_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v_traceState_2558_; lean_object* v_env_2559_; lean_object* v_nextMacroScope_2560_; lean_object* v_ngen_2561_; lean_object* v_auxDeclNGen_2562_; lean_object* v_cache_2563_; lean_object* v_messages_2564_; lean_object* v_infoState_2565_; lean_object* v_snapshotTasks_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2589_; 
v___x_2557_ = lean_st_ref_take(v___y_2520_);
v_traceState_2558_ = lean_ctor_get(v___x_2557_, 4);
v_env_2559_ = lean_ctor_get(v___x_2557_, 0);
v_nextMacroScope_2560_ = lean_ctor_get(v___x_2557_, 1);
v_ngen_2561_ = lean_ctor_get(v___x_2557_, 2);
v_auxDeclNGen_2562_ = lean_ctor_get(v___x_2557_, 3);
v_cache_2563_ = lean_ctor_get(v___x_2557_, 5);
v_messages_2564_ = lean_ctor_get(v___x_2557_, 6);
v_infoState_2565_ = lean_ctor_get(v___x_2557_, 7);
v_snapshotTasks_2566_ = lean_ctor_get(v___x_2557_, 8);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2568_ = v___x_2557_;
v_isShared_2569_ = v_isSharedCheck_2589_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_snapshotTasks_2566_);
lean_inc(v_infoState_2565_);
lean_inc(v_messages_2564_);
lean_inc(v_cache_2563_);
lean_inc(v_traceState_2558_);
lean_inc(v_auxDeclNGen_2562_);
lean_inc(v_ngen_2561_);
lean_inc(v_nextMacroScope_2560_);
lean_inc(v_env_2559_);
lean_dec(v___x_2557_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2589_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
uint64_t v_tid_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2587_; 
v_tid_2570_ = lean_ctor_get_uint64(v_traceState_2558_, sizeof(void*)*1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_traceState_2558_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v_traceState_2558_, 0);
lean_dec(v_unused_2588_);
v___x_2572_ = v_traceState_2558_;
v_isShared_2573_ = v_isSharedCheck_2587_;
goto v_resetjp_2571_;
}
else
{
lean_dec(v_traceState_2558_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2587_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_ref_2515_);
lean_ctor_set(v___x_2574_, 1, v_a_2553_);
v___x_2575_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2513_, v___x_2574_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2575_);
v___x_2577_ = v___x_2572_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2575_);
lean_ctor_set_uint64(v_reuseFailAlloc_2586_, sizeof(void*)*1, v_tid_2570_);
v___x_2577_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 4, v___x_2577_);
v___x_2579_ = v___x_2568_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_env_2559_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_nextMacroScope_2560_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_ngen_2561_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v_auxDeclNGen_2562_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2585_, 5, v_cache_2563_);
lean_ctor_set(v_reuseFailAlloc_2585_, 6, v_messages_2564_);
lean_ctor_set(v_reuseFailAlloc_2585_, 7, v_infoState_2565_);
lean_ctor_set(v_reuseFailAlloc_2585_, 8, v_snapshotTasks_2566_);
v___x_2579_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2580_ = lean_st_ref_set(v___y_2520_, v___x_2579_);
v___x_2581_ = lean_box(0);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2581_);
v___x_2583_ = v___x_2555_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5___redArg___boxed(lean_object* v_oldTraces_2593_, lean_object* v_data_2594_, lean_object* v_ref_2595_, lean_object* v_msg_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5___redArg(v_oldTraces_2593_, v_data_2594_, v_ref_2595_, v_msg_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
return v_res_2602_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__4(lean_object* v_e_2603_){
_start:
{
if (lean_obj_tag(v_e_2603_) == 0)
{
uint8_t v___x_2604_; 
v___x_2604_ = 2;
return v___x_2604_;
}
else
{
uint8_t v___x_2605_; 
v___x_2605_ = 0;
return v___x_2605_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__4___boxed(lean_object* v_e_2606_){
_start:
{
uint8_t v_res_2607_; lean_object* v_r_2608_; 
v_res_2607_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__4(v_e_2606_);
lean_dec_ref(v_e_2606_);
v_r_2608_ = lean_box(v_res_2607_);
return v_r_2608_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6___redArg(lean_object* v_x_2609_){
_start:
{
if (lean_obj_tag(v_x_2609_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
v_a_2611_ = lean_ctor_get(v_x_2609_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_x_2609_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v_x_2609_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v_x_2609_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set_tag(v___x_2613_, 1);
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
v_a_2619_ = lean_ctor_get(v_x_2609_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_x_2609_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v_x_2609_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v_x_2609_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
lean_ctor_set_tag(v___x_2621_, 0);
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6___redArg___boxed(lean_object* v_x_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6___redArg(v_x_2627_);
return v_res_2629_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__0));
v___x_2632_ = l_Lean_stringToMessageData(v___x_2631_);
return v___x_2632_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2633_; double v___x_2634_; 
v___x_2633_ = lean_unsigned_to_nat(1000u);
v___x_2634_ = lean_float_of_nat(v___x_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4(lean_object* v_cls_2635_, uint8_t v_collapsed_2636_, lean_object* v_tag_2637_, lean_object* v_opts_2638_, uint8_t v_clsEnabled_2639_, lean_object* v_oldTraces_2640_, lean_object* v_msg_2641_, lean_object* v_resStartStop_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_fst_2651_; lean_object* v_snd_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2750_; 
v_fst_2651_ = lean_ctor_get(v_resStartStop_2642_, 0);
v_snd_2652_ = lean_ctor_get(v_resStartStop_2642_, 1);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_resStartStop_2642_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2654_ = v_resStartStop_2642_;
v_isShared_2655_ = v_isSharedCheck_2750_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_snd_2652_);
lean_inc(v_fst_2651_);
lean_dec(v_resStartStop_2642_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2750_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v_data_2659_; lean_object* v_fst_2670_; lean_object* v_snd_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2749_; 
v_fst_2670_ = lean_ctor_get(v_snd_2652_, 0);
v_snd_2671_ = lean_ctor_get(v_snd_2652_, 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_snd_2652_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2673_ = v_snd_2652_;
v_isShared_2674_ = v_isSharedCheck_2749_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_snd_2671_);
lean_inc(v_fst_2670_);
lean_dec(v_snd_2652_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2749_;
goto v_resetjp_2672_;
}
v___jp_2656_:
{
lean_object* v___x_2660_; 
v___x_2660_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5___redArg(v_oldTraces_2640_, v_data_2659_, v___y_2658_, v___y_2657_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v___x_2661_; 
lean_dec_ref(v___x_2660_);
v___x_2661_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6___redArg(v_fst_2651_);
return v___x_2661_;
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v_fst_2651_);
v_a_2662_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2660_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2660_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; uint8_t v___x_2676_; lean_object* v___y_2678_; lean_object* v_a_2679_; uint8_t v___y_2703_; double v___y_2734_; 
v___x_2675_ = l_Lean_trace_profiler;
v___x_2676_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_opts_2638_, v___x_2675_);
if (v___x_2676_ == 0)
{
v___y_2703_ = v___x_2676_;
goto v___jp_2702_;
}
else
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2740_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_opts_2638_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; lean_object* v___x_2742_; double v___x_2743_; double v___x_2744_; double v___x_2745_; 
v___x_2741_ = l_Lean_trace_profiler_threshold;
v___x_2742_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__7(v_opts_2638_, v___x_2741_);
v___x_2743_ = lean_float_of_nat(v___x_2742_);
v___x_2744_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__2);
v___x_2745_ = lean_float_div(v___x_2743_, v___x_2744_);
v___y_2734_ = v___x_2745_;
goto v___jp_2733_;
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2747_; double v___x_2748_; 
v___x_2746_ = l_Lean_trace_profiler_threshold;
v___x_2747_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__7(v_opts_2638_, v___x_2746_);
v___x_2748_ = lean_float_of_nat(v___x_2747_);
v___y_2734_ = v___x_2748_;
goto v___jp_2733_;
}
}
v___jp_2677_:
{
uint8_t v_result_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; 
v_result_2680_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__4(v_fst_2651_);
v___x_2681_ = l_Lean_TraceResult_toEmoji(v_result_2680_);
v___x_2682_ = l_Lean_stringToMessageData(v___x_2681_);
v___x_2683_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__7);
if (v_isShared_2674_ == 0)
{
lean_ctor_set_tag(v___x_2673_, 7);
lean_ctor_set(v___x_2673_, 1, v___x_2683_);
lean_ctor_set(v___x_2673_, 0, v___x_2682_);
v___x_2685_ = v___x_2673_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v_m_2687_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set_tag(v___x_2654_, 7);
lean_ctor_set(v___x_2654_, 1, v_a_2679_);
lean_ctor_set(v___x_2654_, 0, v___x_2685_);
v_m_2687_ = v___x_2654_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_a_2679_);
v_m_2687_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; double v___x_2690_; lean_object* v_data_2691_; 
v___x_2688_ = lean_box(v_result_2680_);
v___x_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
v___x_2690_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__0);
lean_inc_ref(v_tag_2637_);
lean_inc_ref(v___x_2689_);
lean_inc(v_cls_2635_);
v_data_2691_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2691_, 0, v_cls_2635_);
lean_ctor_set(v_data_2691_, 1, v___x_2689_);
lean_ctor_set(v_data_2691_, 2, v_tag_2637_);
lean_ctor_set_float(v_data_2691_, sizeof(void*)*3, v___x_2690_);
lean_ctor_set_float(v_data_2691_, sizeof(void*)*3 + 8, v___x_2690_);
lean_ctor_set_uint8(v_data_2691_, sizeof(void*)*3 + 16, v_collapsed_2636_);
if (v___x_2676_ == 0)
{
lean_dec_ref(v___x_2689_);
lean_dec(v_snd_2671_);
lean_dec(v_fst_2670_);
lean_dec_ref(v_tag_2637_);
lean_dec(v_cls_2635_);
v___y_2657_ = v_m_2687_;
v___y_2658_ = v___y_2678_;
v_data_2659_ = v_data_2691_;
goto v___jp_2656_;
}
else
{
lean_object* v_data_2692_; double v___x_2693_; double v___x_2694_; 
lean_dec_ref(v_data_2691_);
v_data_2692_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2692_, 0, v_cls_2635_);
lean_ctor_set(v_data_2692_, 1, v___x_2689_);
lean_ctor_set(v_data_2692_, 2, v_tag_2637_);
v___x_2693_ = lean_unbox_float(v_fst_2670_);
lean_dec(v_fst_2670_);
lean_ctor_set_float(v_data_2692_, sizeof(void*)*3, v___x_2693_);
v___x_2694_ = lean_unbox_float(v_snd_2671_);
lean_dec(v_snd_2671_);
lean_ctor_set_float(v_data_2692_, sizeof(void*)*3 + 8, v___x_2694_);
lean_ctor_set_uint8(v_data_2692_, sizeof(void*)*3 + 16, v_collapsed_2636_);
v___y_2657_ = v_m_2687_;
v___y_2658_ = v___y_2678_;
v_data_2659_ = v_data_2692_;
goto v___jp_2656_;
}
}
}
}
v___jp_2697_:
{
lean_object* v_ref_2698_; lean_object* v___x_2699_; 
v_ref_2698_ = lean_ctor_get(v___y_2648_, 5);
lean_inc(v___y_2649_);
lean_inc_ref(v___y_2648_);
lean_inc(v___y_2647_);
lean_inc_ref(v___y_2646_);
lean_inc(v_fst_2651_);
v___x_2699_ = lean_apply_9(v_msg_2641_, v_fst_2651_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, lean_box(0));
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2699_);
lean_inc(v_ref_2698_);
v___y_2678_ = v_ref_2698_;
v_a_2679_ = v_a_2700_;
goto v___jp_2677_;
}
else
{
lean_object* v___x_2701_; 
lean_dec_ref(v___x_2699_);
v___x_2701_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___closed__1);
lean_inc(v_ref_2698_);
v___y_2678_ = v_ref_2698_;
v_a_2679_ = v___x_2701_;
goto v___jp_2677_;
}
}
v___jp_2702_:
{
if (v_clsEnabled_2639_ == 0)
{
if (v___y_2703_ == 0)
{
lean_object* v___x_2704_; lean_object* v_traceState_2705_; lean_object* v_env_2706_; lean_object* v_nextMacroScope_2707_; lean_object* v_ngen_2708_; lean_object* v_auxDeclNGen_2709_; lean_object* v_cache_2710_; lean_object* v_messages_2711_; lean_object* v_infoState_2712_; lean_object* v_snapshotTasks_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2732_; 
lean_del_object(v___x_2673_);
lean_dec(v_snd_2671_);
lean_dec(v_fst_2670_);
lean_del_object(v___x_2654_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v_msg_2641_);
lean_dec_ref(v_tag_2637_);
lean_dec(v_cls_2635_);
v___x_2704_ = lean_st_ref_take(v___y_2649_);
v_traceState_2705_ = lean_ctor_get(v___x_2704_, 4);
v_env_2706_ = lean_ctor_get(v___x_2704_, 0);
v_nextMacroScope_2707_ = lean_ctor_get(v___x_2704_, 1);
v_ngen_2708_ = lean_ctor_get(v___x_2704_, 2);
v_auxDeclNGen_2709_ = lean_ctor_get(v___x_2704_, 3);
v_cache_2710_ = lean_ctor_get(v___x_2704_, 5);
v_messages_2711_ = lean_ctor_get(v___x_2704_, 6);
v_infoState_2712_ = lean_ctor_get(v___x_2704_, 7);
v_snapshotTasks_2713_ = lean_ctor_get(v___x_2704_, 8);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2715_ = v___x_2704_;
v_isShared_2716_ = v_isSharedCheck_2732_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_snapshotTasks_2713_);
lean_inc(v_infoState_2712_);
lean_inc(v_messages_2711_);
lean_inc(v_cache_2710_);
lean_inc(v_traceState_2705_);
lean_inc(v_auxDeclNGen_2709_);
lean_inc(v_ngen_2708_);
lean_inc(v_nextMacroScope_2707_);
lean_inc(v_env_2706_);
lean_dec(v___x_2704_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2732_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
uint64_t v_tid_2717_; lean_object* v_traces_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2731_; 
v_tid_2717_ = lean_ctor_get_uint64(v_traceState_2705_, sizeof(void*)*1);
v_traces_2718_ = lean_ctor_get(v_traceState_2705_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_traceState_2705_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2720_ = v_traceState_2705_;
v_isShared_2721_ = v_isSharedCheck_2731_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_traces_2718_);
lean_dec(v_traceState_2705_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2731_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2722_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2640_, v_traces_2718_);
lean_dec_ref(v_traces_2718_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2722_);
v___x_2724_ = v___x_2720_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2722_);
lean_ctor_set_uint64(v_reuseFailAlloc_2730_, sizeof(void*)*1, v_tid_2717_);
v___x_2724_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2726_; 
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 4, v___x_2724_);
v___x_2726_ = v___x_2715_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_env_2706_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_nextMacroScope_2707_);
lean_ctor_set(v_reuseFailAlloc_2729_, 2, v_ngen_2708_);
lean_ctor_set(v_reuseFailAlloc_2729_, 3, v_auxDeclNGen_2709_);
lean_ctor_set(v_reuseFailAlloc_2729_, 4, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2729_, 5, v_cache_2710_);
lean_ctor_set(v_reuseFailAlloc_2729_, 6, v_messages_2711_);
lean_ctor_set(v_reuseFailAlloc_2729_, 7, v_infoState_2712_);
lean_ctor_set(v_reuseFailAlloc_2729_, 8, v_snapshotTasks_2713_);
v___x_2726_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = lean_st_ref_set(v___y_2649_, v___x_2726_);
lean_dec(v___y_2649_);
v___x_2728_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6___redArg(v_fst_2651_);
return v___x_2728_;
}
}
}
}
}
else
{
goto v___jp_2697_;
}
}
else
{
goto v___jp_2697_;
}
}
v___jp_2733_:
{
double v___x_2735_; double v___x_2736_; double v___x_2737_; uint8_t v___x_2738_; 
v___x_2735_ = lean_unbox_float(v_snd_2671_);
v___x_2736_ = lean_unbox_float(v_fst_2670_);
v___x_2737_ = lean_float_sub(v___x_2735_, v___x_2736_);
v___x_2738_ = lean_float_decLt(v___y_2734_, v___x_2737_);
v___y_2703_ = v___x_2738_;
goto v___jp_2702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4___boxed(lean_object* v_cls_2751_, lean_object* v_collapsed_2752_, lean_object* v_tag_2753_, lean_object* v_opts_2754_, lean_object* v_clsEnabled_2755_, lean_object* v_oldTraces_2756_, lean_object* v_msg_2757_, lean_object* v_resStartStop_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
uint8_t v_collapsed_boxed_2767_; uint8_t v_clsEnabled_boxed_2768_; lean_object* v_res_2769_; 
v_collapsed_boxed_2767_ = lean_unbox(v_collapsed_2752_);
v_clsEnabled_boxed_2768_ = lean_unbox(v_clsEnabled_2755_);
v_res_2769_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4(v_cls_2751_, v_collapsed_boxed_2767_, v_tag_2753_, v_opts_2754_, v_clsEnabled_boxed_2768_, v_oldTraces_2756_, v_msg_2757_, v_resStartStop_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec_ref(v_opts_2754_);
return v_res_2769_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__0));
v___x_2772_ = l_Lean_stringToMessageData(v___x_2771_);
return v___x_2772_;
}
}
static double _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3(void){
_start:
{
lean_object* v___x_2774_; double v___x_2775_; 
v___x_2774_ = lean_unsigned_to_nat(1000000000u);
v___x_2775_ = lean_float_of_nat(v___x_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(lean_object* v_P_2776_, lean_object* v_lhs_2777_, lean_object* v_rhs_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v_options_2807_; uint8_t v_hasTrace_2808_; lean_object* v_cls_2809_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; uint8_t v_____do__lift_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; 
v_options_2807_ = lean_ctor_get(v_a_2784_, 2);
v_hasTrace_2808_ = lean_ctor_get_uint8(v_options_2807_, sizeof(void*)*1);
v_cls_2809_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
if (v_hasTrace_2808_ == 0)
{
lean_object* v___x_2923_; lean_object* v_a_2924_; uint8_t v___x_2925_; 
v___x_2923_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2809_, v_a_2784_);
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref(v___x_2923_);
v___x_2925_ = lean_unbox(v_a_2924_);
lean_dec(v_a_2924_);
v_____do__lift_2902_ = v___x_2925_;
v___y_2903_ = v_a_2779_;
v___y_2904_ = v_a_2780_;
v___y_2905_ = v_a_2781_;
v___y_2906_ = v_a_2782_;
v___y_2907_ = v_a_2783_;
v___y_2908_ = v_a_2784_;
v___y_2909_ = v_a_2785_;
goto v___jp_2901_;
}
else
{
lean_object* v___x_2926_; lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_3040_; 
v___x_2926_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2809_, v_a_2784_);
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_3040_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_3040_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___f_2931_; uint8_t v___x_2932_; lean_object* v___x_2933_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v_a_2937_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v_a_2950_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v_a_2970_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v_a_2986_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; uint8_t v___x_3034_; 
v___f_2931_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__2));
v___x_2932_ = 0;
v___x_2933_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go_spec__1___closed__1));
v___x_3034_ = lean_unbox(v_a_2927_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_3035_ = l_Lean_trace_profiler;
v___x_3036_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_options_2807_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v_a_3038_; uint8_t v___x_3039_; 
lean_del_object(v___x_2929_);
lean_dec(v_a_2927_);
v___x_3037_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2809_, v_a_2784_);
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref(v___x_3037_);
v___x_3039_ = lean_unbox(v_a_3038_);
lean_dec(v_a_3038_);
v_____do__lift_2902_ = v___x_3039_;
v___y_2903_ = v_a_2779_;
v___y_2904_ = v_a_2780_;
v___y_2905_ = v_a_2781_;
v___y_2906_ = v_a_2782_;
v___y_2907_ = v_a_2783_;
v___y_2908_ = v_a_2784_;
v___y_2909_ = v_a_2785_;
goto v___jp_2901_;
}
else
{
lean_inc_ref(v_options_2807_);
goto v___jp_3001_;
}
}
else
{
lean_inc_ref(v_options_2807_);
goto v___jp_3001_;
}
v___jp_2934_:
{
lean_object* v___x_2938_; double v___x_2939_; double v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; uint8_t v___x_2945_; lean_object* v___x_2946_; 
v___x_2938_ = lean_io_get_num_heartbeats();
v___x_2939_ = lean_float_of_nat(v___y_2935_);
v___x_2940_ = lean_float_of_nat(v___x_2938_);
v___x_2941_ = lean_box_float(v___x_2939_);
v___x_2942_ = lean_box_float(v___x_2940_);
v___x_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
v___x_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2944_, 0, v_a_2937_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = lean_unbox(v_a_2927_);
lean_dec(v_a_2927_);
v___x_2946_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4(v_cls_2809_, v___x_2932_, v___x_2933_, v_options_2807_, v___x_2945_, v___y_2936_, v___f_2931_, v___x_2944_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
lean_dec_ref(v_options_2807_);
return v___x_2946_;
}
v___jp_2947_:
{
lean_object* v___x_2952_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v_a_2950_);
v___x_2952_ = v___x_2929_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2950_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
v___y_2935_ = v___y_2948_;
v___y_2936_ = v___y_2949_;
v_a_2937_ = v___x_2952_;
goto v___jp_2934_;
}
}
v___jp_2954_:
{
if (lean_obj_tag(v___y_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_del_object(v___x_2929_);
v_a_2958_ = lean_ctor_get(v___y_2957_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___y_2957_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___y_2957_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___y_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
lean_ctor_set_tag(v___x_2960_, 1);
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
v___y_2935_ = v___y_2955_;
v___y_2936_ = v___y_2956_;
v_a_2937_ = v___x_2963_;
goto v___jp_2934_;
}
}
}
else
{
lean_object* v_a_2966_; 
v_a_2966_ = lean_ctor_get(v___y_2957_, 0);
lean_inc(v_a_2966_);
lean_dec_ref(v___y_2957_);
v___y_2948_ = v___y_2955_;
v___y_2949_ = v___y_2956_;
v_a_2950_ = v_a_2966_;
goto v___jp_2947_;
}
}
v___jp_2967_:
{
lean_object* v___x_2971_; double v___x_2972_; double v___x_2973_; double v___x_2974_; double v___x_2975_; double v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; lean_object* v___x_2982_; 
v___x_2971_ = lean_io_mono_nanos_now();
v___x_2972_ = lean_float_of_nat(v___y_2969_);
v___x_2973_ = lean_float_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__3);
v___x_2974_ = lean_float_div(v___x_2972_, v___x_2973_);
v___x_2975_ = lean_float_of_nat(v___x_2971_);
v___x_2976_ = lean_float_div(v___x_2975_, v___x_2973_);
v___x_2977_ = lean_box_float(v___x_2974_);
v___x_2978_ = lean_box_float(v___x_2976_);
v___x_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2977_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2980_, 0, v_a_2970_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = lean_unbox(v_a_2927_);
lean_dec(v_a_2927_);
v___x_2982_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4(v_cls_2809_, v___x_2932_, v___x_2933_, v_options_2807_, v___x_2981_, v___y_2968_, v___f_2931_, v___x_2980_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
lean_dec_ref(v_options_2807_);
return v___x_2982_;
}
v___jp_2983_:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v_a_2986_);
v___y_2968_ = v___y_2984_;
v___y_2969_ = v___y_2985_;
v_a_2970_ = v___x_2987_;
goto v___jp_2967_;
}
v___jp_2988_:
{
if (lean_obj_tag(v___y_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
v_a_2992_ = lean_ctor_get(v___y_2991_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___y_2991_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___y_2991_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___y_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
lean_ctor_set_tag(v___x_2994_, 1);
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
v___y_2968_ = v___y_2989_;
v___y_2969_ = v___y_2990_;
v_a_2970_ = v___x_2997_;
goto v___jp_2967_;
}
}
}
else
{
lean_object* v_a_3000_; 
v_a_3000_ = lean_ctor_get(v___y_2991_, 0);
lean_inc(v_a_3000_);
lean_dec_ref(v___y_2991_);
v___y_2984_ = v___y_2989_;
v___y_2985_ = v___y_2990_;
v_a_2986_ = v_a_3000_;
goto v___jp_2983_;
}
}
v___jp_3001_:
{
lean_object* v___x_3002_; lean_object* v_a_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3002_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__2___redArg(v_a_2785_);
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref(v___x_3002_);
v___x_3004_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3005_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__3(v_options_2807_, v___x_3004_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v_a_3008_; uint8_t v___x_3009_; 
lean_del_object(v___x_2929_);
v___x_3006_ = lean_io_mono_nanos_now();
v___x_3007_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2809_, v_a_2784_);
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref(v___x_3007_);
v___x_3009_ = lean_unbox(v_a_3008_);
lean_dec(v_a_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_box(0);
lean_inc(v_a_2785_);
lean_inc_ref(v_a_2784_);
lean_inc(v_a_2783_);
lean_inc_ref(v_a_2782_);
v___x_3011_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(v_lhs_2777_, v_rhs_2778_, v_cls_2809_, v___x_3005_, v_P_2776_, v_hasTrace_2808_, v___x_3010_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
v___y_2989_ = v_a_3003_;
v___y_2990_ = v___x_3006_;
v___y_2991_ = v___x_3011_;
goto v___jp_2988_;
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3012_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1);
lean_inc_ref(v_rhs_2778_);
lean_inc_ref(v_lhs_2777_);
lean_inc_ref(v_P_2776_);
v___x_3013_ = l_Lean_mkAppB(v_P_2776_, v_lhs_2777_, v_rhs_2778_);
v___x_3014_ = l_Lean_indentExpr(v___x_3013_);
v___x_3015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3012_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2809_, v___x_3015_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref(v___x_3016_);
lean_inc(v_a_2785_);
lean_inc_ref(v_a_2784_);
lean_inc(v_a_2783_);
lean_inc_ref(v_a_2782_);
v___x_3018_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3(v_lhs_2777_, v_rhs_2778_, v_cls_2809_, v___x_3005_, v_P_2776_, v_hasTrace_2808_, v_a_3017_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
v___y_2989_ = v_a_3003_;
v___y_2990_ = v___x_3006_;
v___y_2991_ = v___x_3018_;
goto v___jp_2988_;
}
else
{
lean_object* v_a_3019_; 
lean_dec_ref(v_rhs_2778_);
lean_dec_ref(v_lhs_2777_);
lean_dec_ref(v_P_2776_);
v_a_3019_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3019_);
lean_dec_ref(v___x_3016_);
v___y_2984_ = v_a_3003_;
v___y_2985_ = v___x_3006_;
v_a_2986_ = v_a_3019_;
goto v___jp_2983_;
}
}
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v_a_3022_; uint8_t v___x_3023_; 
v___x_3020_ = lean_io_get_num_heartbeats();
v___x_3021_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2809_, v_a_2784_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref(v___x_3021_);
v___x_3023_ = lean_unbox(v_a_3022_);
lean_dec(v_a_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = lean_box(0);
lean_inc(v_a_2785_);
lean_inc_ref(v_a_2784_);
lean_inc(v_a_2783_);
lean_inc_ref(v_a_2782_);
v___x_3025_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__7(v_lhs_2777_, v_rhs_2778_, v_P_2776_, v___x_3005_, v_cls_2809_, v___x_3024_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
v___y_2955_ = v___x_3020_;
v___y_2956_ = v_a_3003_;
v___y_2957_ = v___x_3025_;
goto v___jp_2954_;
}
else
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3026_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1);
lean_inc_ref(v_rhs_2778_);
lean_inc_ref(v_lhs_2777_);
lean_inc_ref(v_P_2776_);
v___x_3027_ = l_Lean_mkAppB(v_P_2776_, v_lhs_2777_, v_rhs_2778_);
v___x_3028_ = l_Lean_indentExpr(v___x_3027_);
v___x_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3026_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2809_, v___x_3029_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref(v___x_3030_);
lean_inc(v_a_2785_);
lean_inc_ref(v_a_2784_);
lean_inc(v_a_2783_);
lean_inc_ref(v_a_2782_);
v___x_3032_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__7(v_lhs_2777_, v_rhs_2778_, v_P_2776_, v___x_3005_, v_cls_2809_, v_a_3031_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
v___y_2955_ = v___x_3020_;
v___y_2956_ = v_a_3003_;
v___y_2957_ = v___x_3032_;
goto v___jp_2954_;
}
else
{
lean_object* v_a_3033_; 
lean_dec_ref(v_rhs_2778_);
lean_dec_ref(v_lhs_2777_);
lean_dec_ref(v_P_2776_);
v_a_3033_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3033_);
lean_dec_ref(v___x_3030_);
v___y_2948_ = v___x_3020_;
v___y_2949_ = v_a_3003_;
v_a_2950_ = v_a_3033_;
goto v___jp_2947_;
}
}
}
}
}
}
v___jp_2787_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2794_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__8);
v___x_2795_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__9));
v___x_2796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2796_, 0, v___y_2789_);
lean_ctor_set(v___x_2796_, 1, v___x_2794_);
lean_ctor_set(v___x_2796_, 2, v___x_2795_);
v___x_2797_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_run_x27___redArg(v___y_2788_, v___x_2796_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
return v___x_2797_;
}
v___jp_2798_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
v___jp_2801_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
return v___x_2803_;
}
v___jp_2804_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
return v___x_2806_;
}
v___jp_2810_:
{
lean_object* v___x_2818_; 
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_inc_ref(v_lhs_2777_);
v___x_2818_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_lhs_2777_);
if (lean_obj_tag(v___x_2818_) == 1)
{
lean_object* v_val_2819_; lean_object* v___x_2820_; 
v_val_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_val_2819_);
lean_dec_ref(v___x_2818_);
lean_inc_ref(v_rhs_2778_);
v___x_2820_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_ofApp2_x3f(v_rhs_2778_);
if (lean_obj_tag(v___x_2820_) == 1)
{
lean_object* v_val_2821_; uint8_t v___x_2822_; 
v_val_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_val_2821_);
lean_dec_ref(v___x_2820_);
v___x_2822_ = lean_expr_eqv(v_val_2819_, v_val_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v_a_2824_; uint8_t v___x_2825_; 
lean_dec_ref(v_P_2776_);
v___x_2823_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2809_, v___y_2816_);
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref(v___x_2823_);
v___x_2825_ = lean_unbox(v_a_2824_);
lean_dec(v_a_2824_);
if (v___x_2825_ == 0)
{
lean_dec(v_val_2821_);
lean_dec(v_val_2819_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec_ref(v_rhs_2778_);
lean_dec_ref(v_lhs_2777_);
goto v___jp_2798_;
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2826_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__2);
v___x_2827_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2819_);
v___x_2828_ = l_Lean_MessageData_ofExpr(v___x_2827_);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2826_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__4);
v___x_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = l_Lean_indentExpr(v_lhs_2777_);
v___x_2833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__6);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2821_);
v___x_2837_ = l_Lean_MessageData_ofExpr(v___x_2836_);
v___x_2838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2835_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
lean_ctor_set(v___x_2839_, 1, v___x_2830_);
v___x_2840_ = l_Lean_indentExpr(v_rhs_2778_);
v___x_2841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2809_, v___x_2841_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_dec_ref(v___x_2842_);
goto v___jp_2798_;
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
else
{
lean_object* v___x_2851_; lean_object* v_a_2852_; lean_object* v___x_2853_; lean_object* v___f_2854_; uint8_t v___x_2855_; 
lean_dec(v_val_2821_);
v___x_2851_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2809_, v___y_2816_);
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v___x_2851_);
v___x_2853_ = lean_box(v___x_2822_);
lean_inc(v_val_2819_);
v___f_2854_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__1___boxed), 11, 5);
lean_closure_set(v___f_2854_, 0, v_val_2819_);
lean_closure_set(v___f_2854_, 1, v_lhs_2777_);
lean_closure_set(v___f_2854_, 2, v_rhs_2778_);
lean_closure_set(v___f_2854_, 3, v_P_2776_);
lean_closure_set(v___f_2854_, 4, v___x_2853_);
v___x_2855_ = lean_unbox(v_a_2852_);
lean_dec(v_a_2852_);
if (v___x_2855_ == 0)
{
v___y_2788_ = v___f_2854_;
v___y_2789_ = v_val_2819_;
v___y_2790_ = v___y_2814_;
v___y_2791_ = v___y_2815_;
v___y_2792_ = v___y_2816_;
v___y_2793_ = v___y_2817_;
goto v___jp_2787_;
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2856_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__11);
lean_inc(v_val_2819_);
v___x_2857_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Op_toExpr(v_val_2819_);
v___x_2858_ = l_Lean_MessageData_ofExpr(v___x_2857_);
v___x_2859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2856_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
v___x_2860_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__13);
v___x_2861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2859_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2809_, v___x_2861_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_dec_ref(v___x_2862_);
v___y_2788_ = v___f_2854_;
v___y_2789_ = v_val_2819_;
v___y_2790_ = v___y_2814_;
v___y_2791_ = v___y_2815_;
v___y_2792_ = v___y_2816_;
v___y_2793_ = v___y_2817_;
goto v___jp_2787_;
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec_ref(v___f_2854_);
lean_dec(v_val_2819_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
}
}
else
{
lean_object* v___x_2871_; lean_object* v_a_2872_; uint8_t v___x_2873_; 
lean_dec(v___x_2820_);
lean_dec(v_val_2819_);
lean_dec_ref(v_lhs_2777_);
lean_dec_ref(v_P_2776_);
v___x_2871_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2809_, v___y_2816_);
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref(v___x_2871_);
v___x_2873_ = lean_unbox(v_a_2872_);
lean_dec(v_a_2872_);
if (v___x_2873_ == 0)
{
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec_ref(v_rhs_2778_);
goto v___jp_2801_;
}
else
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2874_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15);
v___x_2875_ = l_Lean_indentExpr(v_rhs_2778_);
v___x_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2874_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2809_, v___x_2876_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_dec_ref(v___x_2877_);
goto v___jp_2801_;
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2877_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2877_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
}
else
{
lean_object* v___x_2886_; lean_object* v_a_2887_; uint8_t v___x_2888_; 
lean_dec(v___x_2818_);
lean_dec_ref(v_rhs_2778_);
lean_dec_ref(v_P_2776_);
v___x_2886_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2809_, v___y_2816_);
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref(v___x_2886_);
v___x_2888_ = lean_unbox(v_a_2887_);
lean_dec(v_a_2887_);
if (v___x_2888_ == 0)
{
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec_ref(v_lhs_2777_);
goto v___jp_2804_;
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2889_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__15);
v___x_2890_ = l_Lean_indentExpr(v_lhs_2777_);
v___x_2891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2809_, v___x_2891_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_dec_ref(v___x_2892_);
goto v___jp_2804_;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
}
}
v___jp_2901_:
{
if (v_____do__lift_2902_ == 0)
{
v___y_2811_ = v___y_2903_;
v___y_2812_ = v___y_2904_;
v___y_2813_ = v___y_2905_;
v___y_2814_ = v___y_2906_;
v___y_2815_ = v___y_2907_;
v___y_2816_ = v___y_2908_;
v___y_2817_ = v___y_2909_;
goto v___jp_2810_;
}
else
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2910_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___closed__1);
lean_inc_ref(v_rhs_2778_);
lean_inc_ref(v_lhs_2777_);
lean_inc_ref(v_P_2776_);
v___x_2911_ = l_Lean_mkAppB(v_P_2776_, v_lhs_2777_, v_rhs_2778_);
v___x_2912_ = l_Lean_indentExpr(v___x_2911_);
v___x_2913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2910_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_2809_, v___x_2913_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_dec_ref(v___x_2914_);
v___y_2811_ = v___y_2903_;
v___y_2812_ = v___y_2904_;
v___y_2813_ = v___y_2905_;
v___y_2814_ = v___y_2906_;
v___y_2815_ = v___y_2907_;
v___y_2816_ = v___y_2908_;
v___y_2817_ = v___y_2909_;
goto v___jp_2810_;
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v_rhs_2778_);
lean_dec_ref(v_lhs_2777_);
lean_dec_ref(v_P_2776_);
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2914_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2914_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3041_, lean_object* v_lhs_3042_, lean_object* v_rhs_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(v_P_3041_, v_lhs_3042_, v_rhs_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1(lean_object* v_cls_3053_, lean_object* v_msg_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v_cls_3053_, v_msg_3054_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v_cls_3064_, lean_object* v_msg_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1(v_cls_3064_, v_msg_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6(lean_object* v_00_u03b1_3075_, lean_object* v_x_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6___redArg(v_x_3076_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6___boxed(lean_object* v_00_u03b1_3086_, lean_object* v_x_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__6(v_00_u03b1_3086_, v_x_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5(lean_object* v_oldTraces_3097_, lean_object* v_data_3098_, lean_object* v_ref_3099_, lean_object* v_msg_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5___redArg(v_oldTraces_3097_, v_data_3098_, v_ref_3099_, v_msg_3100_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5___boxed(lean_object* v_oldTraces_3110_, lean_object* v_data_3111_, lean_object* v_ref_3112_, lean_object* v_msg_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__4_spec__5(v_oldTraces_3110_, v_data_3111_, v_ref_3112_, v_msg_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
return v_res_3122_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__5));
v___x_3133_ = l_Lean_stringToMessageData(v___x_3132_);
return v___x_3133_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = l_Lean_checkEmoji;
v___x_3135_ = l_Lean_stringToMessageData(v___x_3134_);
return v___x_3135_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__7);
v___x_3137_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__6);
v___x_3138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
lean_ctor_set(v___x_3138_, 1, v___x_3136_);
return v___x_3138_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__9));
v___x_3141_ = l_Lean_stringToMessageData(v___x_3140_);
return v___x_3141_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__10);
v___x_3143_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
lean_ctor_set(v___x_3144_, 1, v___x_3142_);
return v___x_3144_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__12));
v___x_3147_ = l_Lean_stringToMessageData(v___x_3146_);
return v___x_3147_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3148_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__13);
v___x_3149_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__8);
v___x_3150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
lean_ctor_set(v___x_3150_, 1, v___x_3148_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost(lean_object* v_e_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3151_, v_a_3156_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3263_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3263_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3263_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3170_; uint8_t v___x_3171_; 
v___x_3170_ = l_Lean_Expr_cleanupAnnotations(v_a_3161_);
v___x_3171_ = l_Lean_Expr_isApp(v___x_3170_);
if (v___x_3171_ == 0)
{
lean_dec_ref(v___x_3170_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
goto v___jp_3165_;
}
else
{
lean_object* v_arg_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_arg_3172_ = lean_ctor_get(v___x_3170_, 1);
lean_inc_ref(v_arg_3172_);
v___x_3173_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3170_);
v___x_3174_ = l_Lean_Expr_isApp(v___x_3173_);
if (v___x_3174_ == 0)
{
lean_dec_ref(v___x_3173_);
lean_dec_ref(v_arg_3172_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
goto v___jp_3165_;
}
else
{
lean_object* v_arg_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v_arg_3175_ = lean_ctor_get(v___x_3173_, 1);
lean_inc_ref(v_arg_3175_);
v___x_3176_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3173_);
v___x_3177_ = l_Lean_Expr_isApp(v___x_3176_);
if (v___x_3177_ == 0)
{
lean_dec_ref(v___x_3176_);
lean_dec_ref(v_arg_3175_);
lean_dec_ref(v_arg_3172_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
goto v___jp_3165_;
}
else
{
lean_object* v_arg_3178_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___x_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; 
v_arg_3178_ = lean_ctor_get(v___x_3176_, 1);
lean_inc_ref(v_arg_3178_);
v___x_3203_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3176_);
v___x_3204_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1));
v___x_3205_ = l_Lean_Expr_isConstOf(v___x_3203_, v___x_3204_);
if (v___x_3205_ == 0)
{
uint8_t v___x_3206_; 
v___x_3206_ = l_Lean_Expr_isApp(v___x_3203_);
if (v___x_3206_ == 0)
{
lean_dec_ref(v___x_3203_);
lean_dec_ref(v_arg_3178_);
lean_dec_ref(v_arg_3175_);
lean_dec_ref(v_arg_3172_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
goto v___jp_3165_;
}
else
{
lean_object* v_arg_3207_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v_arg_3207_ = lean_ctor_get(v___x_3203_, 1);
lean_inc_ref(v_arg_3207_);
v___x_3232_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3203_);
v___x_3233_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4));
v___x_3234_ = l_Lean_Expr_isConstOf(v___x_3232_, v___x_3233_);
lean_dec_ref(v___x_3232_);
if (v___x_3234_ == 0)
{
lean_dec_ref(v_arg_3207_);
lean_dec_ref(v_arg_3178_);
lean_dec_ref(v_arg_3175_);
lean_dec_ref(v_arg_3172_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
goto v___jp_3165_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v_a_3237_; uint8_t v___x_3238_; 
lean_del_object(v___x_3163_);
v___x_3235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3236_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3235_, v_a_3157_);
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref(v___x_3236_);
v___x_3238_ = lean_unbox(v_a_3237_);
lean_dec(v_a_3237_);
if (v___x_3238_ == 0)
{
v___y_3209_ = v_a_3152_;
v___y_3210_ = v_a_3153_;
v___y_3211_ = v_a_3154_;
v___y_3212_ = v_a_3155_;
v___y_3213_ = v_a_3156_;
v___y_3214_ = v_a_3157_;
v___y_3215_ = v_a_3158_;
goto v___jp_3208_;
}
else
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__11);
v___x_3240_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v___x_3235_, v___x_3239_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_dec_ref(v___x_3240_);
v___y_3209_ = v_a_3152_;
v___y_3210_ = v_a_3153_;
v___y_3211_ = v_a_3154_;
v___y_3212_ = v_a_3155_;
v___y_3213_ = v_a_3156_;
v___y_3214_ = v_a_3157_;
v___y_3215_ = v_a_3158_;
goto v___jp_3208_;
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
lean_dec_ref(v_arg_3207_);
lean_dec_ref(v_arg_3178_);
lean_dec_ref(v_arg_3175_);
lean_dec_ref(v_arg_3172_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3240_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3240_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
}
v___jp_3208_:
{
lean_object* v___x_3216_; 
lean_inc(v___y_3215_);
lean_inc_ref(v___y_3214_);
lean_inc(v___y_3213_);
lean_inc_ref(v___y_3212_);
lean_inc_ref(v_arg_3207_);
v___x_3216_ = l_Lean_Meta_getDecLevel(v_arg_3207_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v_a_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
lean_inc(v_a_3217_);
lean_dec_ref(v___x_3216_);
v___x_3218_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__4));
v___x_3219_ = lean_box(0);
v___x_3220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3220_, 0, v_a_3217_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = l_Lean_Expr_const___override(v___x_3218_, v___x_3220_);
v___x_3222_ = l_Lean_mkAppB(v___x_3221_, v_arg_3207_, v_arg_3178_);
v___x_3223_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(v___x_3222_, v_arg_3175_, v_arg_3172_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
return v___x_3223_;
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v_arg_3207_);
lean_dec_ref(v_arg_3178_);
lean_dec_ref(v_arg_3175_);
lean_dec_ref(v_arg_3172_);
v_a_3224_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3216_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3216_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
}
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v_a_3251_; uint8_t v___x_3252_; 
lean_dec_ref(v___x_3203_);
lean_del_object(v___x_3163_);
v___x_3249_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AC_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3250_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3249_, v_a_3157_);
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref(v___x_3250_);
v___x_3252_ = lean_unbox(v_a_3251_);
lean_dec(v_a_3251_);
if (v___x_3252_ == 0)
{
v___y_3180_ = v_a_3152_;
v___y_3181_ = v_a_3153_;
v___y_3182_ = v_a_3154_;
v___y_3183_ = v_a_3155_;
v___y_3184_ = v_a_3156_;
v___y_3185_ = v_a_3157_;
v___y_3186_ = v_a_3158_;
goto v___jp_3179_;
}
else
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__14);
v___x_3254_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing_spec__1___redArg(v___x_3249_, v___x_3253_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_dec_ref(v___x_3254_);
v___y_3180_ = v_a_3152_;
v___y_3181_ = v_a_3153_;
v___y_3182_ = v_a_3154_;
v___y_3183_ = v_a_3155_;
v___y_3184_ = v_a_3156_;
v___y_3185_ = v_a_3157_;
v___y_3186_ = v_a_3158_;
goto v___jp_3179_;
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v_arg_3178_);
lean_dec_ref(v_arg_3175_);
lean_dec_ref(v_arg_3172_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3254_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
v___jp_3179_:
{
lean_object* v___x_3187_; 
lean_inc(v___y_3186_);
lean_inc_ref(v___y_3185_);
lean_inc(v___y_3184_);
lean_inc_ref(v___y_3183_);
lean_inc_ref(v_arg_3178_);
v___x_3187_ = l_Lean_Meta_getLevel(v_arg_3178_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref(v___x_3187_);
v___x_3189_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___closed__1));
v___x_3190_ = lean_box(0);
v___x_3191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3191_, 0, v_a_3188_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = l_Lean_Expr_const___override(v___x_3189_, v___x_3191_);
v___x_3193_ = l_Lean_Expr_app___override(v___x_3192_, v_arg_3178_);
v___x_3194_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing(v___x_3193_, v_arg_3175_, v_arg_3172_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
return v___x_3194_;
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v_arg_3178_);
lean_dec_ref(v_arg_3175_);
lean_dec_ref(v_arg_3172_);
v_a_3195_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3187_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3187_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
}
}
}
v___jp_3165_:
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3166_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3166_);
v___x_3168_ = v___x_3163_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
v_a_3264_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3160_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3160_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed(lean_object* v_e_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost(v_e_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0(lean_object* v_x_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0___boxed(lean_object* v_x_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__0(v_x_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v_x_3293_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1(lean_object* v_x_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___closed__0));
v___x_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1___boxed(lean_object* v_x_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__1(v_x_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v_x_3316_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2(lean_object* v_e_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3335_, 0, v_e_3326_);
v___x_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2___boxed(lean_object* v_e_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__2(v_e_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3(lean_object* v_x_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = lean_box(0);
v___x_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3___boxed(lean_object* v_x_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___lam__3(v_x_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v_x_3358_);
return v_res_3367_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5(void){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3374_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__5);
v___x_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
return v___x_3376_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7(void){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = lean_unsigned_to_nat(0u);
v___x_3378_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6);
v___x_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
lean_ctor_set(v___x_3379_, 1, v___x_3377_);
return v___x_3379_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8(void){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3380_ = lean_unsigned_to_nat(32u);
v___x_3381_ = lean_mk_empty_array_with_capacity(v___x_3380_);
v___x_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
return v___x_3382_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9(void){
_start:
{
size_t v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3383_ = ((size_t)5ULL);
v___x_3384_ = lean_unsigned_to_nat(0u);
v___x_3385_ = lean_unsigned_to_nat(32u);
v___x_3386_ = lean_mk_empty_array_with_capacity(v___x_3385_);
v___x_3387_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__8);
v___x_3388_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
lean_ctor_set(v___x_3388_, 1, v___x_3386_);
lean_ctor_set(v___x_3388_, 2, v___x_3384_);
lean_ctor_set(v___x_3388_, 3, v___x_3384_);
lean_ctor_set_usize(v___x_3388_, 4, v___x_3383_);
return v___x_3388_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__9);
v___x_3390_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__6);
v___x_3391_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
lean_ctor_set(v___x_3391_, 2, v___x_3390_);
lean_ctor_set(v___x_3391_, 3, v___x_3389_);
return v___x_3391_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3392_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__10);
v___x_3393_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__7);
v___x_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
lean_ctor_set(v___x_3394_, 1, v___x_3392_);
return v___x_3394_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12(void){
_start:
{
uint8_t v___x_3395_; lean_object* v___f_3396_; lean_object* v___f_3397_; lean_object* v___f_3398_; lean_object* v___x_3399_; lean_object* v___f_3400_; lean_object* v___x_3401_; 
v___x_3395_ = 1;
v___f_3396_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4));
v___f_3397_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3));
v___f_3398_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2));
v___x_3399_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed), 9, 0);
v___f_3400_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1));
v___x_3401_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3401_, 0, v___f_3400_);
lean_ctor_set(v___x_3401_, 1, v___x_3399_);
lean_ctor_set(v___x_3401_, 2, v___f_3398_);
lean_ctor_set(v___x_3401_, 3, v___f_3397_);
lean_ctor_set(v___x_3401_, 4, v___f_3396_);
lean_ctor_set_uint8(v___x_3401_, sizeof(void*)*5, v___x_3395_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget(lean_object* v_mvarId_3402_, lean_object* v_maxSteps_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_3407_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3411_; lean_object* v_maxDischargeDepth_3412_; uint8_t v_contextual_3413_; uint8_t v_memoize_3414_; uint8_t v_singlePass_3415_; uint8_t v_zeta_3416_; uint8_t v_beta_3417_; uint8_t v_eta_3418_; uint8_t v_etaStruct_3419_; uint8_t v_iota_3420_; uint8_t v_proj_3421_; uint8_t v_decide_3422_; uint8_t v_arith_3423_; uint8_t v_autoUnfold_3424_; uint8_t v_dsimp_3425_; uint8_t v_failIfUnchanged_3426_; uint8_t v_ground_3427_; uint8_t v_unfoldPartialApp_3428_; uint8_t v_zetaDelta_3429_; uint8_t v_index_3430_; uint8_t v_implicitDefEqProofs_3431_; uint8_t v_zetaUnused_3432_; uint8_t v_catchRuntime_3433_; uint8_t v_zetaHave_3434_; uint8_t v_letToHave_3435_; uint8_t v_congrConsts_3436_; uint8_t v_bitVecOfNat_3437_; uint8_t v_warnExponents_3438_; uint8_t v_suggestions_3439_; lean_object* v_maxSuggestions_3440_; uint8_t v_locals_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3486_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
lean_dec_ref(v___x_3409_);
v___x_3411_ = l_Lean_Meta_Simp_neutralConfig;
v_maxDischargeDepth_3412_ = lean_ctor_get(v___x_3411_, 1);
v_contextual_3413_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3);
v_memoize_3414_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 1);
v_singlePass_3415_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 2);
v_zeta_3416_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 3);
v_beta_3417_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 4);
v_eta_3418_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 5);
v_etaStruct_3419_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 6);
v_iota_3420_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 7);
v_proj_3421_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 8);
v_decide_3422_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 9);
v_arith_3423_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 10);
v_autoUnfold_3424_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 11);
v_dsimp_3425_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 12);
v_failIfUnchanged_3426_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 13);
v_ground_3427_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_3428_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 15);
v_zetaDelta_3429_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 16);
v_index_3430_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_3431_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 18);
v_zetaUnused_3432_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 19);
v_catchRuntime_3433_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 20);
v_zetaHave_3434_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 21);
v_letToHave_3435_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 22);
v_congrConsts_3436_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 23);
v_bitVecOfNat_3437_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 24);
v_warnExponents_3438_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 25);
v_suggestions_3439_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 26);
v_maxSuggestions_3440_ = lean_ctor_get(v___x_3411_, 2);
v_locals_3441_ = lean_ctor_get_uint8(v___x_3411_, sizeof(void*)*3 + 27);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3486_ == 0)
{
lean_object* v_unused_3487_; 
v_unused_3487_ = lean_ctor_get(v___x_3411_, 0);
lean_dec(v_unused_3487_);
v___x_3443_ = v___x_3411_;
v_isShared_3444_ = v_isSharedCheck_3486_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_maxSuggestions_3440_);
lean_inc(v_maxDischargeDepth_3412_);
lean_dec(v___x_3411_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3486_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
uint8_t v___x_3445_; lean_object* v___x_3447_; 
v___x_3445_ = 1;
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v_maxSteps_3403_);
v___x_3447_ = v___x_3443_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_maxSteps_3403_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_maxDischargeDepth_3412_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_maxSuggestions_3440_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3, v_contextual_3413_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 1, v_memoize_3414_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 2, v_singlePass_3415_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 3, v_zeta_3416_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 4, v_beta_3417_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 5, v_eta_3418_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 6, v_etaStruct_3419_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 7, v_iota_3420_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 8, v_proj_3421_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 9, v_decide_3422_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 10, v_arith_3423_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 11, v_autoUnfold_3424_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 12, v_dsimp_3425_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 13, v_failIfUnchanged_3426_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 14, v_ground_3427_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 15, v_unfoldPartialApp_3428_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 16, v_zetaDelta_3429_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 17, v_index_3430_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_3431_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 19, v_zetaUnused_3432_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 20, v_catchRuntime_3433_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 21, v_zetaHave_3434_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 22, v_letToHave_3435_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 23, v_congrConsts_3436_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 24, v_bitVecOfNat_3437_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 25, v_warnExponents_3438_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 26, v_suggestions_3439_);
lean_ctor_set_uint8(v_reuseFailAlloc_3485_, sizeof(void*)*3 + 27, v_locals_3441_);
v___x_3447_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
lean_ctor_set_uint8(v___x_3447_, sizeof(void*)*3 + 28, v___x_3445_);
v___x_3448_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0));
v___x_3449_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3447_, v___x_3448_, v_a_3410_, v_a_3404_, v_a_3406_, v_a_3407_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3451_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref(v___x_3449_);
lean_inc(v_mvarId_3402_);
v___x_3451_ = l_Lean_MVarId_getType(v_mvarId_3402_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3453_; lean_object* v_a_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref(v___x_3451_);
v___x_3453_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_a_3452_, v_a_3405_);
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref(v___x_3453_);
v___x_3455_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11);
v___x_3456_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__12);
lean_inc(v_a_3407_);
lean_inc_ref(v_a_3406_);
lean_inc(v_a_3405_);
lean_inc_ref(v_a_3404_);
lean_inc(v_a_3454_);
v___x_3457_ = l_Lean_Meta_Simp_main(v_a_3454_, v_a_3450_, v___x_3455_, v___x_3456_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v_fst_3459_; lean_object* v___x_3460_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref(v___x_3457_);
v_fst_3459_ = lean_ctor_get(v_a_3458_, 0);
lean_inc(v_fst_3459_);
lean_dec(v_a_3458_);
v___x_3460_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_3402_, v_a_3454_, v_fst_3459_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_);
lean_dec(v_a_3454_);
return v___x_3460_;
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v_a_3454_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_mvarId_3402_);
v_a_3461_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3457_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3457_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec(v_a_3450_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_mvarId_3402_);
v_a_3469_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3451_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3451_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_mvarId_3402_);
v_a_3477_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3449_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3449_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_maxSteps_3403_);
lean_dec(v_mvarId_3402_);
v_a_3488_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3409_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3409_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___boxed(lean_object* v_mvarId_3496_, lean_object* v_maxSteps_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget(v_mvarId_3496_, v_maxSteps_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(lean_object* v_mvarId_3504_, lean_object* v_x_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v___x_3511_; 
v___x_3511_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3504_, v_x_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3511_);
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
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
v_a_3520_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3511_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3511_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg___boxed(lean_object* v_mvarId_3528_, lean_object* v_x_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(v_mvarId_3528_, v_x_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0(lean_object* v_00_u03b1_3536_, lean_object* v_mvarId_3537_, lean_object* v_x_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(v_mvarId_3537_, v_x_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___boxed(lean_object* v_00_u03b1_3545_, lean_object* v_mvarId_3546_, lean_object* v_x_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0(v_00_u03b1_3545_, v_mvarId_3546_, v_x_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4(lean_object* v_maxSteps_3554_, lean_object* v_fvarId_3555_, lean_object* v___f_3556_, lean_object* v___f_3557_, lean_object* v___f_3558_, lean_object* v___f_3559_, lean_object* v_goal_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_3564_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3568_; lean_object* v_maxDischargeDepth_3569_; uint8_t v_contextual_3570_; uint8_t v_memoize_3571_; uint8_t v_singlePass_3572_; uint8_t v_zeta_3573_; uint8_t v_beta_3574_; uint8_t v_eta_3575_; uint8_t v_etaStruct_3576_; uint8_t v_iota_3577_; uint8_t v_proj_3578_; uint8_t v_decide_3579_; uint8_t v_arith_3580_; uint8_t v_autoUnfold_3581_; uint8_t v_dsimp_3582_; uint8_t v_failIfUnchanged_3583_; uint8_t v_ground_3584_; uint8_t v_unfoldPartialApp_3585_; uint8_t v_zetaDelta_3586_; uint8_t v_index_3587_; uint8_t v_implicitDefEqProofs_3588_; uint8_t v_zetaUnused_3589_; uint8_t v_catchRuntime_3590_; uint8_t v_zetaHave_3591_; uint8_t v_letToHave_3592_; uint8_t v_congrConsts_3593_; uint8_t v_bitVecOfNat_3594_; uint8_t v_warnExponents_3595_; uint8_t v_suggestions_3596_; lean_object* v_maxSuggestions_3597_; uint8_t v_locals_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3676_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref(v___x_3566_);
v___x_3568_ = l_Lean_Meta_Simp_neutralConfig;
v_maxDischargeDepth_3569_ = lean_ctor_get(v___x_3568_, 1);
v_contextual_3570_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3);
v_memoize_3571_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 1);
v_singlePass_3572_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 2);
v_zeta_3573_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 3);
v_beta_3574_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 4);
v_eta_3575_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 5);
v_etaStruct_3576_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 6);
v_iota_3577_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 7);
v_proj_3578_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 8);
v_decide_3579_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 9);
v_arith_3580_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 10);
v_autoUnfold_3581_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 11);
v_dsimp_3582_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 12);
v_failIfUnchanged_3583_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 13);
v_ground_3584_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_3585_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 15);
v_zetaDelta_3586_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 16);
v_index_3587_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_3588_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 18);
v_zetaUnused_3589_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 19);
v_catchRuntime_3590_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 20);
v_zetaHave_3591_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 21);
v_letToHave_3592_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 22);
v_congrConsts_3593_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 23);
v_bitVecOfNat_3594_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 24);
v_warnExponents_3595_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 25);
v_suggestions_3596_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 26);
v_maxSuggestions_3597_ = lean_ctor_get(v___x_3568_, 2);
v_locals_3598_ = lean_ctor_get_uint8(v___x_3568_, sizeof(void*)*3 + 27);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3676_ == 0)
{
lean_object* v_unused_3677_; 
v_unused_3677_ = lean_ctor_get(v___x_3568_, 0);
lean_dec(v_unused_3677_);
v___x_3600_ = v___x_3568_;
v_isShared_3601_ = v_isSharedCheck_3676_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_maxSuggestions_3597_);
lean_inc(v_maxDischargeDepth_3569_);
lean_dec(v___x_3568_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3676_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
uint8_t v___x_3602_; lean_object* v___x_3604_; 
v___x_3602_ = 1;
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v_maxSteps_3554_);
v___x_3604_ = v___x_3600_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_maxSteps_3554_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_maxDischargeDepth_3569_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v_maxSuggestions_3597_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3, v_contextual_3570_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 1, v_memoize_3571_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 2, v_singlePass_3572_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 3, v_zeta_3573_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 4, v_beta_3574_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 5, v_eta_3575_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 6, v_etaStruct_3576_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 7, v_iota_3577_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 8, v_proj_3578_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 9, v_decide_3579_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 10, v_arith_3580_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 11, v_autoUnfold_3581_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 12, v_dsimp_3582_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 13, v_failIfUnchanged_3583_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 14, v_ground_3584_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 15, v_unfoldPartialApp_3585_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 16, v_zetaDelta_3586_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 17, v_index_3587_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_3588_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 19, v_zetaUnused_3589_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 20, v_catchRuntime_3590_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 21, v_zetaHave_3591_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 22, v_letToHave_3592_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 23, v_congrConsts_3593_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 24, v_bitVecOfNat_3594_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 25, v_warnExponents_3595_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 26, v_suggestions_3596_);
lean_ctor_set_uint8(v_reuseFailAlloc_3675_, sizeof(void*)*3 + 27, v_locals_3598_);
v___x_3604_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
lean_ctor_set_uint8(v___x_3604_, sizeof(void*)*3 + 28, v___x_3602_);
v___x_3605_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__0));
v___x_3606_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3604_, v___x_3605_, v_a_3567_, v___y_3561_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3608_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref(v___x_3606_);
lean_inc_ref(v___y_3561_);
lean_inc(v_fvarId_3555_);
v___x_3608_ = l_Lean_FVarId_getType___redArg(v_fvarId_3555_, v___y_3561_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v_a_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref(v___x_3608_);
v___x_3610_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_proveEqualityByAC_spec__0___redArg(v_a_3609_, v___y_3562_);
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref(v___x_3610_);
v___x_3612_ = lean_unsigned_to_nat(32u);
v___x_3613_ = lean_mk_empty_array_with_capacity(v___x_3612_);
lean_dec_ref(v___x_3613_);
v___x_3614_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__11);
v___x_3615_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfpost___boxed), 9, 0);
v___x_3616_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3616_, 0, v___f_3556_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
lean_ctor_set(v___x_3616_, 2, v___f_3557_);
lean_ctor_set(v___x_3616_, 3, v___f_3558_);
lean_ctor_set(v___x_3616_, 4, v___f_3559_);
lean_ctor_set_uint8(v___x_3616_, sizeof(void*)*5, v___x_3602_);
lean_inc(v___y_3564_);
lean_inc_ref(v___y_3563_);
lean_inc(v___y_3562_);
lean_inc_ref(v___y_3561_);
v___x_3617_ = l_Lean_Meta_Simp_main(v_a_3611_, v_a_3607_, v___x_3614_, v___x_3616_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v_fst_3619_; uint8_t v___x_3620_; lean_object* v___x_3621_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref(v___x_3617_);
v_fst_3619_ = lean_ctor_get(v_a_3618_, 0);
lean_inc(v_fst_3619_);
lean_dec(v_a_3618_);
v___x_3620_ = 0;
v___x_3621_ = l_Lean_Meta_applySimpResultToLocalDecl(v_goal_3560_, v_fvarId_3555_, v_fst_3619_, v___x_3620_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3642_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3624_ = v___x_3621_;
v_isShared_3625_ = v_isSharedCheck_3642_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3621_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3642_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
if (lean_obj_tag(v_a_3622_) == 0)
{
lean_object* v___x_3626_; lean_object* v___x_3628_; 
v___x_3626_ = lean_box(0);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v___x_3626_);
v___x_3628_ = v___x_3624_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3626_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
else
{
lean_object* v_val_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3641_; 
v_val_3630_ = lean_ctor_get(v_a_3622_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v_a_3622_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3632_ = v_a_3622_;
v_isShared_3633_ = v_isSharedCheck_3641_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_val_3630_);
lean_dec(v_a_3622_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3641_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v_snd_3634_; lean_object* v___x_3636_; 
v_snd_3634_ = lean_ctor_get(v_val_3630_, 1);
lean_inc(v_snd_3634_);
lean_dec(v_val_3630_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 0, v_snd_3634_);
v___x_3636_ = v___x_3632_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_snd_3634_);
v___x_3636_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3638_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v___x_3636_);
v___x_3638_ = v___x_3624_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
}
else
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
v_a_3643_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3621_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3621_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v_goal_3560_);
lean_dec(v_fvarId_3555_);
v_a_3651_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3617_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3617_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec(v_a_3607_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v_goal_3560_);
lean_dec_ref(v___f_3559_);
lean_dec_ref(v___f_3558_);
lean_dec_ref(v___f_3557_);
lean_dec_ref(v___f_3556_);
lean_dec(v_fvarId_3555_);
v_a_3659_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3608_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3608_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v_goal_3560_);
lean_dec_ref(v___f_3559_);
lean_dec_ref(v___f_3558_);
lean_dec_ref(v___f_3557_);
lean_dec_ref(v___f_3556_);
lean_dec(v_fvarId_3555_);
v_a_3667_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3606_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3606_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v_goal_3560_);
lean_dec_ref(v___f_3559_);
lean_dec_ref(v___f_3558_);
lean_dec_ref(v___f_3557_);
lean_dec_ref(v___f_3556_);
lean_dec(v_fvarId_3555_);
lean_dec(v_maxSteps_3554_);
v_a_3678_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3566_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3566_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4___boxed(lean_object* v_maxSteps_3686_, lean_object* v_fvarId_3687_, lean_object* v___f_3688_, lean_object* v___f_3689_, lean_object* v___f_3690_, lean_object* v___f_3691_, lean_object* v_goal_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4(v_maxSteps_3686_, v_fvarId_3687_, v___f_3688_, v___f_3689_, v___f_3690_, v___f_3691_, v_goal_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(lean_object* v_goal_3699_, lean_object* v_fvarId_3700_, lean_object* v_maxSteps_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v___f_3707_; lean_object* v___f_3708_; lean_object* v___f_3709_; lean_object* v___f_3710_; lean_object* v___f_3711_; lean_object* v___x_3712_; 
v___f_3707_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__4));
v___f_3708_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__3));
v___f_3709_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__2));
v___f_3710_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfTarget___closed__1));
lean_inc(v_goal_3699_);
v___f_3711_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___lam__4___boxed), 12, 7);
lean_closure_set(v___f_3711_, 0, v_maxSteps_3701_);
lean_closure_set(v___f_3711_, 1, v_fvarId_3700_);
lean_closure_set(v___f_3711_, 2, v___f_3710_);
lean_closure_set(v___f_3711_, 3, v___f_3709_);
lean_closure_set(v___f_3711_, 4, v___f_3708_);
lean_closure_set(v___f_3711_, 5, v___f_3707_);
lean_closure_set(v___f_3711_, 6, v_goal_3699_);
v___x_3712_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta_spec__0___redArg(v_goal_3699_, v___f_3711_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta___boxed(lean_object* v_goal_3713_, lean_object* v_fvarId_3714_, lean_object* v_maxSteps_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(v_goal_3713_, v_fvarId_3714_, v_maxSteps_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(lean_object* v_x_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = lean_apply_7(v_x_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, lean_box(0));
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed(lean_object* v_x_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(v_x_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(lean_object* v_mvarId_3740_, lean_object* v_x_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___f_3749_; lean_object* v___x_3750_; 
v___f_3749_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3749_, 0, v_x_3741_);
lean_closure_set(v___f_3749_, 1, v___y_3742_);
lean_closure_set(v___f_3749_, 2, v___y_3743_);
v___x_3750_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3740_, v___f_3749_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
if (lean_obj_tag(v___x_3750_) == 0)
{
return v___x_3750_;
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3750_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3750_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg___boxed(lean_object* v_mvarId_3759_, lean_object* v_x_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_mvarId_3759_, v_x_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4(lean_object* v_00_u03b1_3769_, lean_object* v_mvarId_3770_, lean_object* v_x_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_mvarId_3770_, v_x_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___boxed(lean_object* v_00_u03b1_3780_, lean_object* v_mvarId_3781_, lean_object* v_x_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4(v_00_u03b1_3780_, v_mvarId_3781_, v_x_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
return v_res_3790_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(lean_object* v_a_3791_, lean_object* v_x_3792_){
_start:
{
if (lean_obj_tag(v_x_3792_) == 0)
{
uint8_t v___x_3793_; 
v___x_3793_ = 0;
return v___x_3793_;
}
else
{
lean_object* v_key_3794_; lean_object* v_tail_3795_; uint8_t v___x_3796_; 
v_key_3794_ = lean_ctor_get(v_x_3792_, 0);
v_tail_3795_ = lean_ctor_get(v_x_3792_, 2);
v___x_3796_ = l_Lean_instBEqFVarId_beq(v_key_3794_, v_a_3791_);
if (v___x_3796_ == 0)
{
v_x_3792_ = v_tail_3795_;
goto _start;
}
else
{
return v___x_3796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg___boxed(lean_object* v_a_3798_, lean_object* v_x_3799_){
_start:
{
uint8_t v_res_3800_; lean_object* v_r_3801_; 
v_res_3800_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3798_, v_x_3799_);
lean_dec(v_x_3799_);
lean_dec(v_a_3798_);
v_r_3801_ = lean_box(v_res_3800_);
return v_r_3801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_x_3802_, lean_object* v_x_3803_){
_start:
{
if (lean_obj_tag(v_x_3803_) == 0)
{
return v_x_3802_;
}
else
{
lean_object* v_key_3804_; lean_object* v_value_3805_; lean_object* v_tail_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3829_; 
v_key_3804_ = lean_ctor_get(v_x_3803_, 0);
v_value_3805_ = lean_ctor_get(v_x_3803_, 1);
v_tail_3806_ = lean_ctor_get(v_x_3803_, 2);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_x_3803_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3808_ = v_x_3803_;
v_isShared_3809_ = v_isSharedCheck_3829_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_tail_3806_);
lean_inc(v_value_3805_);
lean_inc(v_key_3804_);
lean_dec(v_x_3803_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3829_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3810_; uint64_t v___x_3811_; uint64_t v___x_3812_; uint64_t v___x_3813_; uint64_t v_fold_3814_; uint64_t v___x_3815_; uint64_t v___x_3816_; uint64_t v___x_3817_; size_t v___x_3818_; size_t v___x_3819_; size_t v___x_3820_; size_t v___x_3821_; size_t v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3810_ = lean_array_get_size(v_x_3802_);
v___x_3811_ = l_Lean_instHashableFVarId_hash(v_key_3804_);
v___x_3812_ = 32ULL;
v___x_3813_ = lean_uint64_shift_right(v___x_3811_, v___x_3812_);
v_fold_3814_ = lean_uint64_xor(v___x_3811_, v___x_3813_);
v___x_3815_ = 16ULL;
v___x_3816_ = lean_uint64_shift_right(v_fold_3814_, v___x_3815_);
v___x_3817_ = lean_uint64_xor(v_fold_3814_, v___x_3816_);
v___x_3818_ = lean_uint64_to_usize(v___x_3817_);
v___x_3819_ = lean_usize_of_nat(v___x_3810_);
v___x_3820_ = ((size_t)1ULL);
v___x_3821_ = lean_usize_sub(v___x_3819_, v___x_3820_);
v___x_3822_ = lean_usize_land(v___x_3818_, v___x_3821_);
v___x_3823_ = lean_array_uget_borrowed(v_x_3802_, v___x_3822_);
lean_inc(v___x_3823_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 2, v___x_3823_);
v___x_3825_ = v___x_3808_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_key_3804_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v_value_3805_);
lean_ctor_set(v_reuseFailAlloc_3828_, 2, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_array_uset(v_x_3802_, v___x_3822_, v___x_3825_);
v_x_3802_ = v___x_3826_;
v_x_3803_ = v_tail_3806_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(lean_object* v_i_3830_, lean_object* v_source_3831_, lean_object* v_target_3832_){
_start:
{
lean_object* v___x_3833_; uint8_t v___x_3834_; 
v___x_3833_ = lean_array_get_size(v_source_3831_);
v___x_3834_ = lean_nat_dec_lt(v_i_3830_, v___x_3833_);
if (v___x_3834_ == 0)
{
lean_dec_ref(v_source_3831_);
lean_dec(v_i_3830_);
return v_target_3832_;
}
else
{
lean_object* v_es_3835_; lean_object* v___x_3836_; lean_object* v_source_3837_; lean_object* v_target_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v_es_3835_ = lean_array_fget(v_source_3831_, v_i_3830_);
v___x_3836_ = lean_box(0);
v_source_3837_ = lean_array_fset(v_source_3831_, v_i_3830_, v___x_3836_);
v_target_3838_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(v_target_3832_, v_es_3835_);
v___x_3839_ = lean_unsigned_to_nat(1u);
v___x_3840_ = lean_nat_add(v_i_3830_, v___x_3839_);
lean_dec(v_i_3830_);
v_i_3830_ = v___x_3840_;
v_source_3831_ = v_source_3837_;
v_target_3832_ = v_target_3838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(lean_object* v_data_3842_){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v_nbuckets_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3843_ = lean_array_get_size(v_data_3842_);
v___x_3844_ = lean_unsigned_to_nat(2u);
v_nbuckets_3845_ = lean_nat_mul(v___x_3843_, v___x_3844_);
v___x_3846_ = lean_unsigned_to_nat(0u);
v___x_3847_ = lean_box(0);
v___x_3848_ = lean_mk_array(v_nbuckets_3845_, v___x_3847_);
v___x_3849_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(v___x_3846_, v_data_3842_, v___x_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_m_3850_, lean_object* v_a_3851_, lean_object* v_b_3852_){
_start:
{
lean_object* v_size_3853_; lean_object* v_buckets_3854_; lean_object* v___x_3855_; uint64_t v___x_3856_; uint64_t v___x_3857_; uint64_t v___x_3858_; uint64_t v_fold_3859_; uint64_t v___x_3860_; uint64_t v___x_3861_; uint64_t v___x_3862_; size_t v___x_3863_; size_t v___x_3864_; size_t v___x_3865_; size_t v___x_3866_; size_t v___x_3867_; lean_object* v_bkt_3868_; uint8_t v___x_3869_; 
v_size_3853_ = lean_ctor_get(v_m_3850_, 0);
v_buckets_3854_ = lean_ctor_get(v_m_3850_, 1);
v___x_3855_ = lean_array_get_size(v_buckets_3854_);
v___x_3856_ = l_Lean_instHashableFVarId_hash(v_a_3851_);
v___x_3857_ = 32ULL;
v___x_3858_ = lean_uint64_shift_right(v___x_3856_, v___x_3857_);
v_fold_3859_ = lean_uint64_xor(v___x_3856_, v___x_3858_);
v___x_3860_ = 16ULL;
v___x_3861_ = lean_uint64_shift_right(v_fold_3859_, v___x_3860_);
v___x_3862_ = lean_uint64_xor(v_fold_3859_, v___x_3861_);
v___x_3863_ = lean_uint64_to_usize(v___x_3862_);
v___x_3864_ = lean_usize_of_nat(v___x_3855_);
v___x_3865_ = ((size_t)1ULL);
v___x_3866_ = lean_usize_sub(v___x_3864_, v___x_3865_);
v___x_3867_ = lean_usize_land(v___x_3863_, v___x_3866_);
v_bkt_3868_ = lean_array_uget_borrowed(v_buckets_3854_, v___x_3867_);
v___x_3869_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3851_, v_bkt_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3890_; 
lean_inc_ref(v_buckets_3854_);
lean_inc(v_size_3853_);
v_isSharedCheck_3890_ = !lean_is_exclusive(v_m_3850_);
if (v_isSharedCheck_3890_ == 0)
{
lean_object* v_unused_3891_; lean_object* v_unused_3892_; 
v_unused_3891_ = lean_ctor_get(v_m_3850_, 1);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_m_3850_, 0);
lean_dec(v_unused_3892_);
v___x_3871_ = v_m_3850_;
v_isShared_3872_ = v_isSharedCheck_3890_;
goto v_resetjp_3870_;
}
else
{
lean_dec(v_m_3850_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3890_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3873_; lean_object* v_size_x27_3874_; lean_object* v___x_3875_; lean_object* v_buckets_x27_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; uint8_t v___x_3882_; 
v___x_3873_ = lean_unsigned_to_nat(1u);
v_size_x27_3874_ = lean_nat_add(v_size_3853_, v___x_3873_);
lean_dec(v_size_3853_);
lean_inc(v_bkt_3868_);
v___x_3875_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3875_, 0, v_a_3851_);
lean_ctor_set(v___x_3875_, 1, v_b_3852_);
lean_ctor_set(v___x_3875_, 2, v_bkt_3868_);
v_buckets_x27_3876_ = lean_array_uset(v_buckets_3854_, v___x_3867_, v___x_3875_);
v___x_3877_ = lean_unsigned_to_nat(4u);
v___x_3878_ = lean_nat_mul(v_size_x27_3874_, v___x_3877_);
v___x_3879_ = lean_unsigned_to_nat(3u);
v___x_3880_ = lean_nat_div(v___x_3878_, v___x_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_array_get_size(v_buckets_x27_3876_);
v___x_3882_ = lean_nat_dec_le(v___x_3880_, v___x_3881_);
lean_dec(v___x_3880_);
if (v___x_3882_ == 0)
{
lean_object* v_val_3883_; lean_object* v___x_3885_; 
v_val_3883_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(v_buckets_x27_3876_);
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 1, v_val_3883_);
lean_ctor_set(v___x_3871_, 0, v_size_x27_3874_);
v___x_3885_ = v___x_3871_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_size_x27_3874_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v_val_3883_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
else
{
lean_object* v___x_3888_; 
if (v_isShared_3872_ == 0)
{
lean_ctor_set(v___x_3871_, 1, v_buckets_x27_3876_);
lean_ctor_set(v___x_3871_, 0, v_size_x27_3874_);
v___x_3888_ = v___x_3871_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_size_x27_3874_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v_buckets_x27_3876_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
else
{
lean_dec(v_b_3852_);
lean_dec(v_a_3851_);
return v_m_3850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(lean_object* v_as_3893_, size_t v_i_3894_, size_t v_stop_3895_, lean_object* v_b_3896_, lean_object* v___y_3897_){
_start:
{
uint8_t v___x_3899_; 
v___x_3899_ = lean_usize_dec_eq(v_i_3894_, v_stop_3895_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; lean_object* v_rewriteCache_3901_; lean_object* v_acNfCache_3902_; lean_object* v_typeAnalysis_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3917_; 
v___x_3900_ = lean_st_ref_take(v___y_3897_);
v_rewriteCache_3901_ = lean_ctor_get(v___x_3900_, 0);
v_acNfCache_3902_ = lean_ctor_get(v___x_3900_, 1);
v_typeAnalysis_3903_ = lean_ctor_get(v___x_3900_, 2);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3905_ = v___x_3900_;
v_isShared_3906_ = v_isSharedCheck_3917_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_typeAnalysis_3903_);
lean_inc(v_acNfCache_3902_);
lean_inc(v_rewriteCache_3901_);
lean_dec(v___x_3900_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3917_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3907_ = lean_array_uget_borrowed(v_as_3893_, v_i_3894_);
v___x_3908_ = lean_box(0);
lean_inc(v___x_3907_);
v___x_3909_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(v_acNfCache_3902_, v___x_3907_, v___x_3908_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 1, v___x_3909_);
v___x_3911_ = v___x_3905_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_rewriteCache_3901_);
lean_ctor_set(v_reuseFailAlloc_3916_, 1, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3916_, 2, v_typeAnalysis_3903_);
v___x_3911_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3912_; size_t v___x_3913_; size_t v___x_3914_; 
v___x_3912_ = lean_st_ref_set(v___y_3897_, v___x_3911_);
v___x_3913_ = ((size_t)1ULL);
v___x_3914_ = lean_usize_add(v_i_3894_, v___x_3913_);
v_i_3894_ = v___x_3914_;
v_b_3896_ = v___x_3908_;
goto _start;
}
}
}
else
{
lean_object* v___x_3918_; 
v___x_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3918_, 0, v_b_3896_);
return v___x_3918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg___boxed(lean_object* v_as_3919_, lean_object* v_i_3920_, lean_object* v_stop_3921_, lean_object* v_b_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
size_t v_i_boxed_3925_; size_t v_stop_boxed_3926_; lean_object* v_res_3927_; 
v_i_boxed_3925_ = lean_unbox_usize(v_i_3920_);
lean_dec(v_i_3920_);
v_stop_boxed_3926_ = lean_unbox_usize(v_stop_3921_);
lean_dec(v_stop_3921_);
v_res_3927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_as_3919_, v_i_boxed_3925_, v_stop_boxed_3926_, v_b_3922_, v___y_3923_);
lean_dec(v___y_3923_);
lean_dec_ref(v_as_3919_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0(lean_object* v___x_3928_, size_t v___x_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_Meta_getPropHyps(v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3956_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3940_ = v___x_3937_;
v_isShared_3941_ = v_isSharedCheck_3956_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3937_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3956_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; 
v___x_3942_ = lean_array_get_size(v_a_3938_);
v___x_3943_ = lean_box(0);
v___x_3944_ = lean_nat_dec_lt(v___x_3928_, v___x_3942_);
if (v___x_3944_ == 0)
{
lean_object* v___x_3946_; 
lean_dec(v_a_3938_);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3943_);
v___x_3946_ = v___x_3940_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3943_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
else
{
uint8_t v___x_3948_; 
v___x_3948_ = lean_nat_dec_le(v___x_3942_, v___x_3942_);
if (v___x_3948_ == 0)
{
if (v___x_3944_ == 0)
{
lean_object* v___x_3950_; 
lean_dec(v_a_3938_);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3943_);
v___x_3950_ = v___x_3940_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3943_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
else
{
size_t v___x_3952_; lean_object* v___x_3953_; 
lean_del_object(v___x_3940_);
v___x_3952_ = lean_usize_of_nat(v___x_3942_);
v___x_3953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_a_3938_, v___x_3929_, v___x_3952_, v___x_3943_, v___y_3931_);
lean_dec(v_a_3938_);
return v___x_3953_;
}
}
else
{
size_t v___x_3954_; lean_object* v___x_3955_; 
lean_del_object(v___x_3940_);
v___x_3954_ = lean_usize_of_nat(v___x_3942_);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_a_3938_, v___x_3929_, v___x_3954_, v___x_3943_, v___y_3931_);
lean_dec(v_a_3938_);
return v___x_3955_;
}
}
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
v_a_3957_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3937_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3937_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v___x_3965_, lean_object* v___x_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
size_t v___x_8696__boxed_3974_; lean_object* v_res_3975_; 
v___x_8696__boxed_3974_ = lean_unbox_usize(v___x_3966_);
lean_dec(v___x_3966_);
v_res_3975_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__0(v___x_3965_, v___x_8696__boxed_3974_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___x_3965_);
return v_res_3975_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_m_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v_buckets_3978_; lean_object* v___x_3979_; uint64_t v___x_3980_; uint64_t v___x_3981_; uint64_t v___x_3982_; uint64_t v_fold_3983_; uint64_t v___x_3984_; uint64_t v___x_3985_; uint64_t v___x_3986_; size_t v___x_3987_; size_t v___x_3988_; size_t v___x_3989_; size_t v___x_3990_; size_t v___x_3991_; lean_object* v___x_3992_; uint8_t v___x_3993_; 
v_buckets_3978_ = lean_ctor_get(v_m_3976_, 1);
v___x_3979_ = lean_array_get_size(v_buckets_3978_);
v___x_3980_ = l_Lean_instHashableFVarId_hash(v_a_3977_);
v___x_3981_ = 32ULL;
v___x_3982_ = lean_uint64_shift_right(v___x_3980_, v___x_3981_);
v_fold_3983_ = lean_uint64_xor(v___x_3980_, v___x_3982_);
v___x_3984_ = 16ULL;
v___x_3985_ = lean_uint64_shift_right(v_fold_3983_, v___x_3984_);
v___x_3986_ = lean_uint64_xor(v_fold_3983_, v___x_3985_);
v___x_3987_ = lean_uint64_to_usize(v___x_3986_);
v___x_3988_ = lean_usize_of_nat(v___x_3979_);
v___x_3989_ = ((size_t)1ULL);
v___x_3990_ = lean_usize_sub(v___x_3988_, v___x_3989_);
v___x_3991_ = lean_usize_land(v___x_3987_, v___x_3990_);
v___x_3992_ = lean_array_uget_borrowed(v_buckets_3978_, v___x_3991_);
v___x_3993_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3977_, v___x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_m_3994_, lean_object* v_a_3995_){
_start:
{
uint8_t v_res_3996_; lean_object* v_r_3997_; 
v_res_3996_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(v_m_3994_, v_a_3995_);
lean_dec(v_a_3995_);
lean_dec_ref(v_m_3994_);
v_r_3997_ = lean_box(v_res_3996_);
return v_r_3997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(lean_object* v_as_3998_, size_t v_i_3999_, size_t v_stop_4000_, lean_object* v_b_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v_a_4005_; uint8_t v___x_4009_; 
v___x_4009_ = lean_usize_dec_eq(v_i_3999_, v_stop_4000_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; lean_object* v_acNfCache_4011_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v___x_4010_ = lean_st_ref_get(v___y_4002_);
v_acNfCache_4011_ = lean_ctor_get(v___x_4010_, 1);
lean_inc_ref(v_acNfCache_4011_);
lean_dec(v___x_4010_);
v___x_4012_ = lean_array_uget_borrowed(v_as_3998_, v_i_3999_);
v___x_4013_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(v_acNfCache_4011_, v___x_4012_);
lean_dec_ref(v_acNfCache_4011_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; 
lean_inc(v___x_4012_);
v___x_4014_ = lean_array_push(v_b_4001_, v___x_4012_);
v_a_4005_ = v___x_4014_;
goto v___jp_4004_;
}
else
{
v_a_4005_ = v_b_4001_;
goto v___jp_4004_;
}
}
else
{
lean_object* v___x_4015_; 
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v_b_4001_);
return v___x_4015_;
}
v___jp_4004_:
{
size_t v___x_4006_; size_t v___x_4007_; 
v___x_4006_ = ((size_t)1ULL);
v___x_4007_ = lean_usize_add(v_i_3999_, v___x_4006_);
v_i_3999_ = v___x_4007_;
v_b_4001_ = v_a_4005_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg___boxed(lean_object* v_as_4016_, lean_object* v_i_4017_, lean_object* v_stop_4018_, lean_object* v_b_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
size_t v_i_boxed_4022_; size_t v_stop_boxed_4023_; lean_object* v_res_4024_; 
v_i_boxed_4022_ = lean_unbox_usize(v_i_4017_);
lean_dec(v_i_4017_);
v_stop_boxed_4023_ = lean_unbox_usize(v_stop_4018_);
lean_dec(v_stop_4018_);
v_res_4024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_as_4016_, v_i_boxed_4022_, v_stop_boxed_4023_, v_b_4019_, v___y_4020_);
lean_dec(v___y_4020_);
lean_dec_ref(v_as_4016_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_as_4025_, size_t v_sz_4026_, size_t v_i_4027_, lean_object* v_b_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
uint8_t v___x_4035_; 
v___x_4035_ = lean_usize_dec_lt(v_i_4027_, v_sz_4026_);
if (v___x_4035_ == 0)
{
lean_object* v___x_4036_; 
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec_ref(v___y_4029_);
v___x_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4036_, 0, v_b_4028_);
return v___x_4036_;
}
else
{
lean_object* v_maxSteps_4037_; lean_object* v_a_4038_; lean_object* v___x_4039_; 
v_maxSteps_4037_ = lean_ctor_get(v___y_4029_, 1);
v_a_4038_ = lean_array_uget_borrowed(v_as_4025_, v_i_4027_);
lean_inc(v___y_4033_);
lean_inc_ref(v___y_4032_);
lean_inc(v___y_4031_);
lean_inc_ref(v___y_4030_);
lean_inc(v_maxSteps_4037_);
lean_inc(v_a_4038_);
lean_inc(v_b_4028_);
v___x_4039_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNfHypMeta(v_b_4028_, v_a_4038_, v_maxSteps_4037_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v_a_4042_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref(v___x_4039_);
if (lean_obj_tag(v_a_4040_) == 1)
{
lean_object* v_val_4046_; 
lean_dec(v_b_4028_);
v_val_4046_ = lean_ctor_get(v_a_4040_, 0);
lean_inc(v_val_4046_);
lean_dec_ref(v_a_4040_);
v_a_4042_ = v_val_4046_;
goto v___jp_4041_;
}
else
{
lean_dec(v_a_4040_);
v_a_4042_ = v_b_4028_;
goto v___jp_4041_;
}
v___jp_4041_:
{
size_t v___x_4043_; size_t v___x_4044_; 
v___x_4043_ = ((size_t)1ULL);
v___x_4044_ = lean_usize_add(v_i_4027_, v___x_4043_);
v_i_4027_ = v___x_4044_;
v_b_4028_ = v_a_4042_;
goto _start;
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v_b_4028_);
v_a_4047_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4039_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4039_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_as_4055_, lean_object* v_sz_4056_, lean_object* v_i_4057_, lean_object* v_b_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
size_t v_sz_boxed_4065_; size_t v_i_boxed_4066_; lean_object* v_res_4067_; 
v_sz_boxed_4065_ = lean_unbox_usize(v_sz_4056_);
lean_dec(v_sz_4056_);
v_i_boxed_4066_ = lean_unbox_usize(v_i_4057_);
lean_dec(v_i_4057_);
v_res_4067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(v_as_4055_, v_sz_boxed_4065_, v_i_boxed_4066_, v_b_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
lean_dec_ref(v_as_4055_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1(lean_object* v_goal_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v___x_4083_; 
lean_inc(v___y_4081_);
lean_inc_ref(v___y_4080_);
lean_inc(v___y_4079_);
lean_inc_ref(v___y_4078_);
v___x_4083_ = l_Lean_Meta_getPropHyps(v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v___x_4085_; lean_object* v_a_4087_; lean_object* v___y_4120_; lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref(v___x_4083_);
v___x_4085_ = lean_unsigned_to_nat(0u);
v___x_4130_ = lean_array_get_size(v_a_4084_);
v___x_4131_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__1));
v___x_4132_ = lean_nat_dec_lt(v___x_4085_, v___x_4130_);
if (v___x_4132_ == 0)
{
lean_dec(v_a_4084_);
v_a_4087_ = v___x_4131_;
goto v___jp_4086_;
}
else
{
uint8_t v___x_4133_; 
v___x_4133_ = lean_nat_dec_le(v___x_4130_, v___x_4130_);
if (v___x_4133_ == 0)
{
if (v___x_4132_ == 0)
{
lean_dec(v_a_4084_);
v_a_4087_ = v___x_4131_;
goto v___jp_4086_;
}
else
{
size_t v___x_4134_; size_t v___x_4135_; lean_object* v___x_4136_; 
v___x_4134_ = ((size_t)0ULL);
v___x_4135_ = lean_usize_of_nat(v___x_4130_);
v___x_4136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_a_4084_, v___x_4134_, v___x_4135_, v___x_4131_, v___y_4077_);
lean_dec(v_a_4084_);
v___y_4120_ = v___x_4136_;
goto v___jp_4119_;
}
}
else
{
size_t v___x_4137_; size_t v___x_4138_; lean_object* v___x_4139_; 
v___x_4137_ = ((size_t)0ULL);
v___x_4138_ = lean_usize_of_nat(v___x_4130_);
v___x_4139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_a_4084_, v___x_4137_, v___x_4138_, v___x_4131_, v___y_4077_);
lean_dec(v_a_4084_);
v___y_4120_ = v___x_4139_;
goto v___jp_4119_;
}
}
v___jp_4086_:
{
size_t v_sz_4088_; size_t v___x_4089_; lean_object* v___x_4090_; 
v_sz_4088_ = lean_array_size(v_a_4087_);
v___x_4089_ = ((size_t)0ULL);
lean_inc(v___y_4081_);
lean_inc_ref(v___y_4080_);
lean_inc(v___y_4079_);
lean_inc_ref(v___y_4078_);
lean_inc_ref(v___y_4076_);
v___x_4090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(v_a_4087_, v_sz_4088_, v___x_4089_, v_goal_4075_, v___y_4076_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec_ref(v_a_4087_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___f_4092_; lean_object* v___x_4093_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref(v___x_4090_);
v___f_4092_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___closed__0));
lean_inc(v_a_4091_);
v___x_4093_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_a_4091_, v___f_4092_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4101_; 
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4101_ == 0)
{
lean_object* v_unused_4102_; 
v_unused_4102_ = lean_ctor_get(v___x_4093_, 0);
lean_dec(v_unused_4102_);
v___x_4095_ = v___x_4093_;
v_isShared_4096_ = v_isSharedCheck_4101_;
goto v_resetjp_4094_;
}
else
{
lean_dec(v___x_4093_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4101_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4097_; lean_object* v___x_4099_; 
v___x_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4097_, 0, v_a_4091_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_4097_);
v___x_4099_ = v___x_4095_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4097_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec(v_a_4091_);
v_a_4103_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4093_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4093_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
v_a_4111_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4090_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4090_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
v___jp_4119_:
{
if (lean_obj_tag(v___y_4120_) == 0)
{
lean_object* v_a_4121_; 
v_a_4121_ = lean_ctor_get(v___y_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref(v___y_4120_);
v_a_4087_ = v_a_4121_;
goto v___jp_4086_;
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v_goal_4075_);
v_a_4122_ = lean_ctor_get(v___y_4120_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___y_4120_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___y_4120_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___y_4120_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v_goal_4075_);
v_a_4140_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4083_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4083_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v_goal_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1(v_goal_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2(lean_object* v_goal_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v___f_4165_; lean_object* v___x_4166_; 
lean_inc(v_goal_4157_);
v___f_4165_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4165_, 0, v_goal_4157_);
v___x_4166_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__4___redArg(v_goal_4157_, v___f_4165_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2___boxed(lean_object* v_goal_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass___lam__2(v_goal_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
return v_res_4175_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0(lean_object* v_00_u03b2_4184_, lean_object* v_m_4185_, lean_object* v_a_4186_){
_start:
{
uint8_t v___x_4187_; 
v___x_4187_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___redArg(v_m_4185_, v_a_4186_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_00_u03b2_4188_, lean_object* v_m_4189_, lean_object* v_a_4190_){
_start:
{
uint8_t v_res_4191_; lean_object* v_r_4192_; 
v_res_4191_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0(v_00_u03b2_4188_, v_m_4189_, v_a_4190_);
lean_dec(v_a_4190_);
lean_dec_ref(v_m_4189_);
v_r_4192_ = lean_box(v_res_4191_);
return v_r_4192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1(lean_object* v_00_u03b2_4193_, lean_object* v_m_4194_, lean_object* v_a_4195_, lean_object* v_b_4196_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1___redArg(v_m_4194_, v_a_4195_, v_b_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2(lean_object* v_as_4198_, size_t v_sz_4199_, size_t v_i_4200_, lean_object* v_b_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v___x_4209_; 
v___x_4209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___redArg(v_as_4198_, v_sz_4199_, v_i_4200_, v_b_4201_, v___y_4202_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_as_4210_, lean_object* v_sz_4211_, lean_object* v_i_4212_, lean_object* v_b_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
size_t v_sz_boxed_4221_; size_t v_i_boxed_4222_; lean_object* v_res_4223_; 
v_sz_boxed_4221_ = lean_unbox_usize(v_sz_4211_);
lean_dec(v_sz_4211_);
v_i_boxed_4222_ = lean_unbox_usize(v_i_4212_);
lean_dec(v_i_4212_);
v_res_4223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__2(v_as_4210_, v_sz_boxed_4221_, v_i_boxed_4222_, v_b_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
lean_dec(v___y_4215_);
lean_dec_ref(v_as_4210_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3(lean_object* v_as_4224_, size_t v_i_4225_, size_t v_stop_4226_, lean_object* v_b_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___redArg(v_as_4224_, v_i_4225_, v_stop_4226_, v_b_4227_, v___y_4229_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3___boxed(lean_object* v_as_4236_, lean_object* v_i_4237_, lean_object* v_stop_4238_, lean_object* v_b_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
size_t v_i_boxed_4247_; size_t v_stop_boxed_4248_; lean_object* v_res_4249_; 
v_i_boxed_4247_ = lean_unbox_usize(v_i_4237_);
lean_dec(v_i_4237_);
v_stop_boxed_4248_ = lean_unbox_usize(v_stop_4238_);
lean_dec(v_stop_4238_);
v_res_4249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__3(v_as_4236_, v_i_boxed_4247_, v_stop_boxed_4248_, v_b_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec_ref(v_as_4236_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5(lean_object* v_as_4250_, size_t v_i_4251_, size_t v_stop_4252_, lean_object* v_b_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v___x_4261_; 
v___x_4261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___redArg(v_as_4250_, v_i_4251_, v_stop_4252_, v_b_4253_, v___y_4255_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5___boxed(lean_object* v_as_4262_, lean_object* v_i_4263_, lean_object* v_stop_4264_, lean_object* v_b_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
size_t v_i_boxed_4273_; size_t v_stop_boxed_4274_; lean_object* v_res_4275_; 
v_i_boxed_4273_ = lean_unbox_usize(v_i_4263_);
lean_dec(v_i_4263_);
v_stop_boxed_4274_ = lean_unbox_usize(v_stop_4264_);
lean_dec(v_stop_4264_);
v_res_4275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__5(v_as_4262_, v_i_boxed_4273_, v_stop_boxed_4274_, v_b_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec_ref(v_as_4262_);
return v_res_4275_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0(lean_object* v_00_u03b2_4276_, lean_object* v_a_4277_, lean_object* v_x_4278_){
_start:
{
uint8_t v___x_4279_; 
v___x_4279_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_4277_, v_x_4278_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4280_, lean_object* v_a_4281_, lean_object* v_x_4282_){
_start:
{
uint8_t v_res_4283_; lean_object* v_r_4284_; 
v_res_4283_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__0_spec__0(v_00_u03b2_4280_, v_a_4281_, v_x_4282_);
lean_dec(v_x_4282_);
lean_dec(v_a_4281_);
v_r_4284_ = lean_box(v_res_4283_);
return v_r_4284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2(lean_object* v_00_u03b2_4285_, lean_object* v_data_4286_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(v_data_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4288_, lean_object* v_i_4289_, lean_object* v_source_4290_, lean_object* v_target_4291_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(v_i_4289_, v_source_4290_, v_target_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4293_, lean_object* v_x_4294_, lean_object* v_x_4295_){
_start:
{
lean_object* v___x_4296_; 
v___x_4296_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(v_x_4294_, v_x_4295_);
return v___x_4296_;
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
