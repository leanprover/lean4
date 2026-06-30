// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.AC
// Imports: import Lean.Meta.Tactic.AC.Main public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_checkEmoji;
lean_object* l_Lean_stringToMessageData(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
double lean_float_of_nat(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Option_merge___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMul"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 82, 7, 193, 128, 145, 145, 228)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Meta.Tactic.BVDecide.Normalize.Op.mul"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "internal error (this is a bug!): index "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = " out of range, the current state only has "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " variables:\n\n"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Found binary operation '"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "', expected '"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "'.Treating as atom."};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "canonicalizeWithSharing"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Operations mismatch:\n      the left-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n        "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\n      but the right-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Canonicalizing with respect to operation: '"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to recognize operation: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Canonicalizing: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_ac_nf "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " found `BEq.beq`."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " found `Eq`."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__13;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__2___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__3___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__10;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__0___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__0___boxed__const__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__0___boxed__const__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed, .m_arity = 9, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__0___boxed__const__1_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__0_value;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__2___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_ac_nf"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 2, 240, 42, 244, 93, 182, 215)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__3_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType(lean_object* v_w_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__2);
v___x_9_ = l_Lean_Expr_app___override(v___x_8_, v_w_7_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__2(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = lean_box(0);
v___x_15_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__1));
v___x_16_ = l_Lean_Expr_const___override(v___x_15_, v___x_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul(lean_object* v_w_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul___closed__2);
v___x_19_ = l_Lean_Expr_app___override(v___x_18_, v_w_17_);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__3(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__2));
v___x_27_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__1));
v___x_28_ = l_Lean_mkConst(v___x_27_, v___x_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul(lean_object* v_w_29_){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_30_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul___closed__3);
lean_inc_ref(v_w_29_);
v___x_31_ = l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType(v_w_29_);
v___x_32_ = l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstMul(v_w_29_);
v___x_33_ = l_Lean_mkAppB(v___x_30_, v___x_31_, v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__2(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_box(0);
v___x_39_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__1));
v___x_40_ = l_Lean_mkConst(v___x_39_, v___x_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit(lean_object* v_w_41_, lean_object* v_n_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit___closed__2);
v___x_44_ = l_Lean_mkNatLit(v_n_42_);
v___x_45_ = l_Lean_mkAppB(v___x_43_, v_w_41_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = lean_expr_eqv(v_x_46_, v_x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq___boxed(lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq(v_x_49_, v_x_50_);
lean_dec_ref(v_x_50_);
lean_dec_ref(v_x_49_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(2u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_to_int(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr(lean_object* v_x_65_, lean_object* v_prec_66_){
_start:
{
lean_object* v___y_68_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1024u);
v___x_78_ = lean_nat_dec_le(v___x_77_, v_prec_66_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3);
v___y_68_ = v___x_79_;
goto v___jp_67_;
}
else
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4);
v___y_68_ = v___x_80_;
goto v___jp_67_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_69_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__2));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___boxed(lean_object* v_x_81_, lean_object* v_prec_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr(v_x_81_, v_prec_82_);
lean_dec(v_prec_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(lean_object* v_e_91_){
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
v___x_106_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2));
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
v___x_114_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(lean_object* v_x_118_){
_start:
{
if (lean_obj_tag(v_x_118_) == 5)
{
lean_object* v_fn_119_; 
v_fn_119_ = lean_ctor_get(v_x_118_, 0);
lean_inc_ref(v_fn_119_);
lean_dec_ref_known(v_x_118_, 2);
if (lean_obj_tag(v_fn_119_) == 5)
{
lean_object* v_fn_120_; lean_object* v___x_121_; 
v_fn_120_ = lean_ctor_get(v_fn_119_, 0);
lean_inc_ref(v_fn_120_);
lean_dec_ref_known(v_fn_119_, 2);
v___x_121_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(v_fn_120_);
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
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = l_Lean_Level_ofNat(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
v___x_127_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0);
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1);
v___x_130_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2);
v___x_133_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0);
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3);
v___x_136_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2));
v___x_137_ = l_Lean_mkConst(v___x_136_, v___x_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(lean_object* v_x_138_){
_start:
{
lean_object* v_bv_139_; lean_object* v_inst_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
lean_inc_ref(v_x_138_);
v_bv_139_ = l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType(v_x_138_);
v_inst_140_ = l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul(v_x_138_);
v___x_141_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4);
lean_inc_ref_n(v_bv_139_, 2);
v___x_142_ = l_Lean_mkApp4(v___x_141_, v_bv_139_, v_bv_139_, v_bv_139_, v_inst_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(lean_object* v_x_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit(v_x_143_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(lean_object* v_op_x27_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(v_op_x27_146_);
if (lean_obj_tag(v___x_147_) == 1)
{
uint8_t v___x_148_; 
lean_dec_ref_known(v___x_147_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg___boxed(lean_object* v_op_x27_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_op_x27_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind(lean_object* v_op_153_, lean_object* v_op_x27_154_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_op_x27_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___boxed(lean_object* v_op_156_, lean_object* v_op_x27_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind(v_op_156_, v_op_x27_157_);
lean_dec_ref(v_op_156_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___lam__0(lean_object* v_op_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_160_);
v___x_162_ = l_Lean_MessageData_ofExpr(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(lean_object* v_x_165_, lean_object* v_s_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg___boxed(lean_object* v_x_190_, lean_object* v_s_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v_x_190_, v_s_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(lean_object* v_00_u03b1_198_, lean_object* v_x_199_, lean_object* v_s_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v_x_199_, v_s_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___boxed(lean_object* v_00_u03b1_207_, lean_object* v_x_208_, lean_object* v_s_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(v_00_u03b1_207_, v_x_208_, v_s_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(lean_object* v_a_216_, lean_object* v_b_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_dec(v_b_217_);
lean_dec_ref(v_a_216_);
return v_x_218_;
}
else
{
lean_object* v_key_219_; lean_object* v_value_220_; lean_object* v_tail_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_233_; 
v_key_219_ = lean_ctor_get(v_x_218_, 0);
v_value_220_ = lean_ctor_get(v_x_218_, 1);
v_tail_221_ = lean_ctor_get(v_x_218_, 2);
v_isSharedCheck_233_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_233_ == 0)
{
v___x_223_ = v_x_218_;
v_isShared_224_ = v_isSharedCheck_233_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_tail_221_);
lean_inc(v_value_220_);
lean_inc(v_key_219_);
lean_dec(v_x_218_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_233_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint8_t v___x_225_; 
v___x_225_ = lean_expr_eqv(v_key_219_, v_a_216_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_216_, v_b_217_, v_tail_221_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 2, v___x_226_);
v___x_228_ = v___x_223_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_key_219_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_value_220_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
else
{
lean_object* v___x_231_; 
lean_dec(v_value_220_);
lean_dec(v_key_219_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v_b_217_);
lean_ctor_set(v___x_223_, 0, v_a_216_);
v___x_231_ = v___x_223_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_216_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_b_217_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_tail_221_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object* v_a_234_, lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
uint8_t v___x_236_; 
v___x_236_ = 0;
return v___x_236_;
}
else
{
lean_object* v_key_237_; lean_object* v_tail_238_; uint8_t v___x_239_; 
v_key_237_ = lean_ctor_get(v_x_235_, 0);
v_tail_238_ = lean_ctor_get(v_x_235_, 2);
v___x_239_ = lean_expr_eqv(v_key_237_, v_a_234_);
if (v___x_239_ == 0)
{
v_x_235_ = v_tail_238_;
goto _start;
}
else
{
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object* v_a_241_, lean_object* v_x_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_241_, v_x_242_);
lean_dec(v_x_242_);
lean_dec_ref(v_a_241_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
return v_x_245_;
}
else
{
lean_object* v_key_247_; lean_object* v_value_248_; lean_object* v_tail_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_272_; 
v_key_247_ = lean_ctor_get(v_x_246_, 0);
v_value_248_ = lean_ctor_get(v_x_246_, 1);
v_tail_249_ = lean_ctor_get(v_x_246_, 2);
v_isSharedCheck_272_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_272_ == 0)
{
v___x_251_ = v_x_246_;
v_isShared_252_ = v_isSharedCheck_272_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_tail_249_);
lean_inc(v_value_248_);
lean_inc(v_key_247_);
lean_dec(v_x_246_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_272_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; uint64_t v___x_254_; uint64_t v___x_255_; uint64_t v___x_256_; uint64_t v_fold_257_; uint64_t v___x_258_; uint64_t v___x_259_; uint64_t v___x_260_; size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_253_ = lean_array_get_size(v_x_245_);
v___x_254_ = l_Lean_Expr_hash(v_key_247_);
v___x_255_ = 32ULL;
v___x_256_ = lean_uint64_shift_right(v___x_254_, v___x_255_);
v_fold_257_ = lean_uint64_xor(v___x_254_, v___x_256_);
v___x_258_ = 16ULL;
v___x_259_ = lean_uint64_shift_right(v_fold_257_, v___x_258_);
v___x_260_ = lean_uint64_xor(v_fold_257_, v___x_259_);
v___x_261_ = lean_uint64_to_usize(v___x_260_);
v___x_262_ = lean_usize_of_nat(v___x_253_);
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_sub(v___x_262_, v___x_263_);
v___x_265_ = lean_usize_land(v___x_261_, v___x_264_);
v___x_266_ = lean_array_uget_borrowed(v_x_245_, v___x_265_);
lean_inc(v___x_266_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 2, v___x_266_);
v___x_268_ = v___x_251_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_key_247_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_value_248_);
lean_ctor_set(v_reuseFailAlloc_271_, 2, v___x_266_);
v___x_268_ = v_reuseFailAlloc_271_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; 
v___x_269_ = lean_array_uset(v_x_245_, v___x_265_, v___x_268_);
v_x_245_ = v___x_269_;
v_x_246_ = v_tail_249_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(lean_object* v_i_273_, lean_object* v_source_274_, lean_object* v_target_275_){
_start:
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = lean_array_get_size(v_source_274_);
v___x_277_ = lean_nat_dec_lt(v_i_273_, v___x_276_);
if (v___x_277_ == 0)
{
lean_dec_ref(v_source_274_);
lean_dec(v_i_273_);
return v_target_275_;
}
else
{
lean_object* v_es_278_; lean_object* v___x_279_; lean_object* v_source_280_; lean_object* v_target_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_es_278_ = lean_array_fget(v_source_274_, v_i_273_);
v___x_279_ = lean_box(0);
v_source_280_ = lean_array_fset(v_source_274_, v_i_273_, v___x_279_);
v_target_281_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_275_, v_es_278_);
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_add(v_i_273_, v___x_282_);
lean_dec(v_i_273_);
v_i_273_ = v___x_283_;
v_source_274_ = v_source_280_;
v_target_275_ = v_target_281_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(lean_object* v_data_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_nbuckets_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_286_ = lean_array_get_size(v_data_285_);
v___x_287_ = lean_unsigned_to_nat(2u);
v_nbuckets_288_ = lean_nat_mul(v___x_286_, v___x_287_);
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_box(0);
v___x_291_ = lean_mk_array(v_nbuckets_288_, v___x_290_);
v___x_292_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v___x_289_, v_data_285_, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object* v_m_293_, lean_object* v_a_294_, lean_object* v_b_295_){
_start:
{
lean_object* v_size_296_; lean_object* v_buckets_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_340_; 
v_size_296_ = lean_ctor_get(v_m_293_, 0);
v_buckets_297_ = lean_ctor_get(v_m_293_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_m_293_);
if (v_isSharedCheck_340_ == 0)
{
v___x_299_ = v_m_293_;
v_isShared_300_ = v_isSharedCheck_340_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_buckets_297_);
lean_inc(v_size_296_);
lean_dec(v_m_293_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_340_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; uint64_t v___x_302_; uint64_t v___x_303_; uint64_t v___x_304_; uint64_t v_fold_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v___x_308_; size_t v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; lean_object* v_bkt_314_; uint8_t v___x_315_; 
v___x_301_ = lean_array_get_size(v_buckets_297_);
v___x_302_ = l_Lean_Expr_hash(v_a_294_);
v___x_303_ = 32ULL;
v___x_304_ = lean_uint64_shift_right(v___x_302_, v___x_303_);
v_fold_305_ = lean_uint64_xor(v___x_302_, v___x_304_);
v___x_306_ = 16ULL;
v___x_307_ = lean_uint64_shift_right(v_fold_305_, v___x_306_);
v___x_308_ = lean_uint64_xor(v_fold_305_, v___x_307_);
v___x_309_ = lean_uint64_to_usize(v___x_308_);
v___x_310_ = lean_usize_of_nat(v___x_301_);
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_sub(v___x_310_, v___x_311_);
v___x_313_ = lean_usize_land(v___x_309_, v___x_312_);
v_bkt_314_ = lean_array_uget_borrowed(v_buckets_297_, v___x_313_);
v___x_315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_294_, v_bkt_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v_size_x27_317_; lean_object* v___x_318_; lean_object* v_buckets_x27_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_316_ = lean_unsigned_to_nat(1u);
v_size_x27_317_ = lean_nat_add(v_size_296_, v___x_316_);
lean_dec(v_size_296_);
lean_inc(v_bkt_314_);
v___x_318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_318_, 0, v_a_294_);
lean_ctor_set(v___x_318_, 1, v_b_295_);
lean_ctor_set(v___x_318_, 2, v_bkt_314_);
v_buckets_x27_319_ = lean_array_uset(v_buckets_297_, v___x_313_, v___x_318_);
v___x_320_ = lean_unsigned_to_nat(4u);
v___x_321_ = lean_nat_mul(v_size_x27_317_, v___x_320_);
v___x_322_ = lean_unsigned_to_nat(3u);
v___x_323_ = lean_nat_div(v___x_321_, v___x_322_);
lean_dec(v___x_321_);
v___x_324_ = lean_array_get_size(v_buckets_x27_319_);
v___x_325_ = lean_nat_dec_le(v___x_323_, v___x_324_);
lean_dec(v___x_323_);
if (v___x_325_ == 0)
{
lean_object* v_val_326_; lean_object* v___x_328_; 
v_val_326_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_buckets_x27_319_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_val_326_);
lean_ctor_set(v___x_299_, 0, v_size_x27_317_);
v___x_328_ = v___x_299_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_size_x27_317_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_val_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
else
{
lean_object* v___x_331_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_buckets_x27_319_);
lean_ctor_set(v___x_299_, 0, v_size_x27_317_);
v___x_331_ = v___x_299_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_size_x27_317_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_buckets_x27_319_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
else
{
lean_object* v___x_333_; lean_object* v_buckets_x27_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_inc(v_bkt_314_);
v___x_333_ = lean_box(0);
v_buckets_x27_334_ = lean_array_uset(v_buckets_297_, v___x_313_, v___x_333_);
v___x_335_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_294_, v_b_295_, v_bkt_314_);
v___x_336_ = lean_array_uset(v_buckets_x27_334_, v___x_313_, v___x_335_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_336_);
v___x_338_ = v___x_299_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_size_296_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object* v_a_341_, lean_object* v_x_342_){
_start:
{
if (lean_obj_tag(v_x_342_) == 0)
{
lean_object* v___x_343_; 
v___x_343_ = lean_box(0);
return v___x_343_;
}
else
{
lean_object* v_key_344_; lean_object* v_value_345_; lean_object* v_tail_346_; uint8_t v___x_347_; 
v_key_344_ = lean_ctor_get(v_x_342_, 0);
v_value_345_ = lean_ctor_get(v_x_342_, 1);
v_tail_346_ = lean_ctor_get(v_x_342_, 2);
v___x_347_ = lean_expr_eqv(v_key_344_, v_a_341_);
if (v___x_347_ == 0)
{
v_x_342_ = v_tail_346_;
goto _start;
}
else
{
lean_object* v___x_349_; 
lean_inc(v_value_345_);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v_value_345_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_350_, lean_object* v_x_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_350_, v_x_351_);
lean_dec(v_x_351_);
lean_dec_ref(v_a_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object* v_m_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_buckets_355_; lean_object* v___x_356_; uint64_t v___x_357_; uint64_t v___x_358_; uint64_t v___x_359_; uint64_t v_fold_360_; uint64_t v___x_361_; uint64_t v___x_362_; uint64_t v___x_363_; size_t v___x_364_; size_t v___x_365_; size_t v___x_366_; size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_buckets_355_ = lean_ctor_get(v_m_353_, 1);
v___x_356_ = lean_array_get_size(v_buckets_355_);
v___x_357_ = l_Lean_Expr_hash(v_a_354_);
v___x_358_ = 32ULL;
v___x_359_ = lean_uint64_shift_right(v___x_357_, v___x_358_);
v_fold_360_ = lean_uint64_xor(v___x_357_, v___x_359_);
v___x_361_ = 16ULL;
v___x_362_ = lean_uint64_shift_right(v_fold_360_, v___x_361_);
v___x_363_ = lean_uint64_xor(v_fold_360_, v___x_362_);
v___x_364_ = lean_uint64_to_usize(v___x_363_);
v___x_365_ = lean_usize_of_nat(v___x_356_);
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_sub(v___x_365_, v___x_366_);
v___x_368_ = lean_usize_land(v___x_364_, v___x_367_);
v___x_369_ = lean_array_uget_borrowed(v_buckets_355_, v___x_368_);
v___x_370_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_354_, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object* v_m_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_371_, v_a_372_);
lean_dec_ref(v_a_372_);
lean_dec_ref(v_m_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(lean_object* v_e_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_op_377_; lean_object* v_exprToVarIndex_378_; lean_object* v_varToExpr_379_; lean_object* v___x_380_; 
v_op_377_ = lean_ctor_get(v_a_375_, 0);
v_exprToVarIndex_378_ = lean_ctor_get(v_a_375_, 1);
v_varToExpr_379_ = lean_ctor_get(v_a_375_, 2);
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_exprToVarIndex_378_, v_e_374_);
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
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_exprToVarIndex_378_, v_e_374_, v_size_384_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object* v_e_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_405_, v_a_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(lean_object* v_e_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_409_, v_a_410_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___boxed(lean_object* v_e_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(v_e_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(lean_object* v_00_u03b2_425_, lean_object* v_m_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_426_, v_a_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object* v_00_u03b2_429_, lean_object* v_m_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(v_00_u03b2_429_, v_m_430_, v_a_431_);
lean_dec_ref(v_a_431_);
lean_dec_ref(v_m_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1(lean_object* v_00_u03b2_433_, lean_object* v_m_434_, lean_object* v_a_435_, lean_object* v_b_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_m_434_, v_a_435_, v_b_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object* v_00_u03b2_438_, lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_439_, v_x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_442_, lean_object* v_a_443_, lean_object* v_x_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(v_00_u03b2_442_, v_a_443_, v_x_444_);
lean_dec(v_x_444_);
lean_dec_ref(v_a_443_);
return v_res_445_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object* v_00_u03b2_446_, lean_object* v_a_447_, lean_object* v_x_448_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_447_, v_x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_450_, lean_object* v_a_451_, lean_object* v_x_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(v_00_u03b2_450_, v_a_451_, v_x_452_);
lean_dec(v_x_452_);
lean_dec_ref(v_a_451_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3(lean_object* v_00_u03b2_455_, lean_object* v_data_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_data_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4(lean_object* v_00_u03b2_458_, lean_object* v_a_459_, lean_object* v_b_460_, lean_object* v_x_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_459_, v_b_460_, v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_463_, lean_object* v_i_464_, lean_object* v_source_465_, lean_object* v_target_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v_i_464_, v_source_465_, v_target_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object* v_msgData_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object* v_msgData_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msgData_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object* v_msg_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_ref_500_; lean_object* v___x_501_; lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_510_; 
v_ref_500_ = lean_ctor_get(v___y_497_, 5);
v___x_501_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object* v_msg_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(lean_object* v_a_518_, lean_object* v_a_519_){
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
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(lean_object* v_idx_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
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
v___x_551_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1);
v___x_552_ = l_Nat_reprFast(v_idx_541_);
v___x_553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
v___x_554_ = l_Lean_MessageData_ofFormat(v___x_553_);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_551_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3);
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
v___x_562_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5);
v___x_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_array_to_list(v_varToExpr_548_);
v___x_565_ = lean_box(0);
v___x_566_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(v___x_564_, v___x_565_);
v___x_567_ = l_Lean_MessageData_ofList(v___x_566_);
v___x_568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_563_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v___x_568_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___boxed(lean_object* v_idx_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(v_idx_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_object* v_00_u03b1_581_, lean_object* v_msg_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_582_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object* v_00_u03b1_590_, lean_object* v_msg_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(v_00_u03b1_590_, v_msg_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec_ref(v___y_592_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object* v_c_599_){
_start:
{
lean_object* v___y_601_; 
if (lean_obj_tag(v_c_599_) == 0)
{
lean_object* v___x_605_; 
v___x_605_ = lean_unsigned_to_nat(0u);
v___y_601_ = v___x_605_;
goto v___jp_600_;
}
else
{
lean_object* v_val_606_; 
v_val_606_ = lean_ctor_get(v_c_599_, 0);
v___y_601_ = v_val_606_;
goto v___jp_600_;
}
v___jp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_add(v___y_601_, v___x_602_);
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object* v_c_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v_c_607_);
lean_dec(v_c_607_);
return v_res_608_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_box(0);
v___x_610_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object* v_a_611_, lean_object* v_x_612_){
_start:
{
if (lean_obj_tag(v_x_612_) == 0)
{
lean_object* v___x_613_; lean_object* v_val_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0);
v_val_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_val_614_);
v___x_615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_615_, 0, v_a_611_);
lean_ctor_set(v___x_615_, 1, v_val_614_);
lean_ctor_set(v___x_615_, 2, v_x_612_);
return v___x_615_;
}
else
{
lean_object* v_key_616_; lean_object* v_value_617_; lean_object* v_tail_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_633_; 
v_key_616_ = lean_ctor_get(v_x_612_, 0);
v_value_617_ = lean_ctor_get(v_x_612_, 1);
v_tail_618_ = lean_ctor_get(v_x_612_, 2);
v_isSharedCheck_633_ = !lean_is_exclusive(v_x_612_);
if (v_isSharedCheck_633_ == 0)
{
v___x_620_ = v_x_612_;
v_isShared_621_ = v_isSharedCheck_633_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_tail_618_);
lean_inc(v_value_617_);
lean_inc(v_key_616_);
lean_dec(v_x_612_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_633_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint8_t v___x_622_; 
v___x_622_ = lean_nat_dec_eq(v_key_616_, v_a_611_);
if (v___x_622_ == 0)
{
lean_object* v_tail_623_; lean_object* v___x_625_; 
v_tail_623_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_611_, v_tail_618_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 2, v_tail_623_);
v___x_625_ = v___x_620_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_key_616_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_value_617_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_tail_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_val_629_; lean_object* v___x_631_; 
lean_dec(v_key_616_);
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v_value_617_);
v___x_628_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_627_);
lean_dec_ref_known(v___x_627_, 1);
v_val_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_val_629_);
lean_dec(v___x_628_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v_val_629_);
lean_ctor_set(v___x_620_, 0, v_a_611_);
v___x_631_ = v___x_620_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_611_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_val_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_tail_618_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
return v_x_634_;
}
else
{
lean_object* v_key_636_; lean_object* v_value_637_; lean_object* v_tail_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_661_; 
v_key_636_ = lean_ctor_get(v_x_635_, 0);
v_value_637_ = lean_ctor_get(v_x_635_, 1);
v_tail_638_ = lean_ctor_get(v_x_635_, 2);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_635_);
if (v_isSharedCheck_661_ == 0)
{
v___x_640_ = v_x_635_;
v_isShared_641_ = v_isSharedCheck_661_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_tail_638_);
lean_inc(v_value_637_);
lean_inc(v_key_636_);
lean_dec(v_x_635_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_661_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; uint64_t v___x_643_; uint64_t v___x_644_; uint64_t v___x_645_; uint64_t v_fold_646_; uint64_t v___x_647_; uint64_t v___x_648_; uint64_t v___x_649_; size_t v___x_650_; size_t v___x_651_; size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_642_ = lean_array_get_size(v_x_634_);
v___x_643_ = lean_uint64_of_nat(v_key_636_);
v___x_644_ = 32ULL;
v___x_645_ = lean_uint64_shift_right(v___x_643_, v___x_644_);
v_fold_646_ = lean_uint64_xor(v___x_643_, v___x_645_);
v___x_647_ = 16ULL;
v___x_648_ = lean_uint64_shift_right(v_fold_646_, v___x_647_);
v___x_649_ = lean_uint64_xor(v_fold_646_, v___x_648_);
v___x_650_ = lean_uint64_to_usize(v___x_649_);
v___x_651_ = lean_usize_of_nat(v___x_642_);
v___x_652_ = ((size_t)1ULL);
v___x_653_ = lean_usize_sub(v___x_651_, v___x_652_);
v___x_654_ = lean_usize_land(v___x_650_, v___x_653_);
v___x_655_ = lean_array_uget_borrowed(v_x_634_, v___x_654_);
lean_inc(v___x_655_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 2, v___x_655_);
v___x_657_ = v___x_640_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_key_636_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_value_637_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v___x_655_);
v___x_657_ = v_reuseFailAlloc_660_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; 
v___x_658_ = lean_array_uset(v_x_634_, v___x_654_, v___x_657_);
v_x_634_ = v___x_658_;
v_x_635_ = v_tail_638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_662_, lean_object* v_source_663_, lean_object* v_target_664_){
_start:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = lean_array_get_size(v_source_663_);
v___x_666_ = lean_nat_dec_lt(v_i_662_, v___x_665_);
if (v___x_666_ == 0)
{
lean_dec_ref(v_source_663_);
lean_dec(v_i_662_);
return v_target_664_;
}
else
{
lean_object* v_es_667_; lean_object* v___x_668_; lean_object* v_source_669_; lean_object* v_target_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_es_667_ = lean_array_fget(v_source_663_, v_i_662_);
v___x_668_ = lean_box(0);
v_source_669_ = lean_array_fset(v_source_663_, v_i_662_, v___x_668_);
v_target_670_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_664_, v_es_667_);
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_nat_add(v_i_662_, v___x_671_);
lean_dec(v_i_662_);
v_i_662_ = v___x_672_;
v_source_663_ = v_source_669_;
v_target_664_ = v_target_670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object* v_data_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_nbuckets_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_675_ = lean_array_get_size(v_data_674_);
v___x_676_ = lean_unsigned_to_nat(2u);
v_nbuckets_677_ = lean_nat_mul(v___x_675_, v___x_676_);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_box(0);
v___x_680_ = lean_mk_array(v_nbuckets_677_, v___x_679_);
v___x_681_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v___x_678_, v_data_674_, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object* v_a_682_, lean_object* v_x_683_){
_start:
{
if (lean_obj_tag(v_x_683_) == 0)
{
uint8_t v___x_684_; 
v___x_684_ = 0;
return v___x_684_;
}
else
{
lean_object* v_key_685_; lean_object* v_tail_686_; uint8_t v___x_687_; 
v_key_685_ = lean_ctor_get(v_x_683_, 0);
v_tail_686_ = lean_ctor_get(v_x_683_, 2);
v___x_687_ = lean_nat_dec_eq(v_key_685_, v_a_682_);
if (v___x_687_ == 0)
{
v_x_683_ = v_tail_686_;
goto _start;
}
else
{
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_689_, lean_object* v_x_690_){
_start:
{
uint8_t v_res_691_; lean_object* v_r_692_; 
v_res_691_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_689_, v_x_690_);
lean_dec(v_x_690_);
lean_dec(v_a_689_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object* v_m_693_, lean_object* v_a_694_){
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
v___x_714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_694_, v_bkt_713_);
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
v_val_725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_718_);
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
v_bkt_x27_734_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_694_, v_bkt_713_);
v___x_741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_694_, v_bkt_x27_734_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object* v_coeff_745_, lean_object* v_e_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_767_; 
v___x_749_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_746_, v_a_747_);
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
v___x_759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(v_coeff_745_, v_fst_754_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object* v_coeff_768_, lean_object* v_e_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_768_, v_e_769_, v_a_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object* v_coeff_773_, lean_object* v_e_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_773_, v_e_774_, v_a_775_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object* v_coeff_782_, lean_object* v_e_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(v_coeff_782_, v_e_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
return v_res_790_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object* v_00_u03b2_791_, lean_object* v_a_792_, lean_object* v_x_793_){
_start:
{
uint8_t v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_795_, lean_object* v_a_796_, lean_object* v_x_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(v_00_u03b2_795_, v_a_796_, v_x_797_);
lean_dec(v_x_797_);
lean_dec(v_a_796_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object* v_00_u03b2_800_, lean_object* v_data_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_data_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_803_, lean_object* v_i_804_, lean_object* v_source_805_, lean_object* v_target_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v_i_804_, v_source_805_, v_target_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_809_, v_x_810_);
return v___x_811_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_812_; double v___x_813_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = lean_float_of_nat(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_817_, lean_object* v_msg_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_ref_825_; lean_object* v___x_826_; lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_872_; 
v_ref_825_ = lean_ctor_get(v___y_822_, 5);
v___x_826_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_818_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
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
v___x_850_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
v___x_851_ = 0;
v___x_852_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_853_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_853_, 0, v_cls_817_);
lean_ctor_set(v___x_853_, 1, v___x_849_);
lean_ctor_set(v___x_853_, 2, v___x_852_);
lean_ctor_set_float(v___x_853_, sizeof(void*)*3, v___x_850_);
lean_ctor_set_float(v___x_853_, sizeof(void*)*3 + 8, v___x_850_);
lean_ctor_set_uint8(v___x_853_, sizeof(void*)*3 + 16, v___x_851_);
v___x_854_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2));
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_873_, lean_object* v_msg_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_873_, v_msg_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6(void){
_start:
{
lean_object* v_cls_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_cls_892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_894_ = l_Lean_Name_append(v___x_893_, v_cls_892_);
return v___x_894_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7));
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_907_, lean_object* v_coeff_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
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
v___x_920_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_fn_918_);
if (v___x_920_ == 0)
{
lean_object* v_options_921_; uint8_t v_hasTrace_922_; 
v_options_921_ = lean_ctor_get(v_a_913_, 2);
v_hasTrace_922_ = lean_ctor_get_uint8(v_options_921_, sizeof(void*)*1);
if (v_hasTrace_922_ == 0)
{
lean_object* v___x_923_; 
lean_dec_ref(v_op_907_);
v___x_923_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_a_910_);
return v___x_923_;
}
else
{
lean_object* v_inheritedTraceOptions_924_; lean_object* v_cls_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_inheritedTraceOptions_924_ = lean_ctor_get(v_a_913_, 13);
v_cls_925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_926_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_927_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_924_, v_options_921_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
lean_dec_ref(v_op_907_);
v___x_928_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_a_910_);
return v___x_928_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_929_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_918_);
v___x_930_ = l_Lean_MessageData_ofExpr(v_fn_918_);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10);
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
v___x_939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_907_);
v___x_942_ = l_Lean_MessageData_ofExpr(v___x_941_);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_940_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_925_, v___x_945_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v_snd_948_; lean_object* v___x_949_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v_snd_948_ = lean_ctor_get(v_a_947_, 1);
lean_inc(v_snd_948_);
lean_dec(v_a_947_);
v___x_949_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_snd_948_);
return v___x_949_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref_known(v_a_909_, 2);
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
lean_dec_ref_known(v_a_909_, 2);
lean_inc_ref(v_op_907_);
v___x_958_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_907_, v_coeff_908_, v_arg_919_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
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
v___x_963_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_a_910_);
return v___x_963_;
}
}
else
{
lean_object* v___x_964_; 
lean_dec_ref(v_op_907_);
v___x_964_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_908_, v_a_909_, v_a_910_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_965_, lean_object* v_coeff_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_965_, v_coeff_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
return v_res_974_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_box(0);
v___x_976_ = lean_unsigned_to_nat(16u);
v___x_977_ = lean_mk_array(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___x_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object* v_op_981_, lean_object* v_e_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_990_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_981_, v___x_989_, v_e_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_991_, lean_object* v_e_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_op_991_, v_e_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1000_, lean_object* v_x_1001_){
_start:
{
if (lean_obj_tag(v_x_1001_) == 0)
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_box(0);
return v___x_1002_;
}
else
{
lean_object* v_key_1003_; lean_object* v_value_1004_; lean_object* v_tail_1005_; uint8_t v___x_1006_; 
v_key_1003_ = lean_ctor_get(v_x_1001_, 0);
v_value_1004_ = lean_ctor_get(v_x_1001_, 1);
v_tail_1005_ = lean_ctor_get(v_x_1001_, 2);
v___x_1006_ = lean_nat_dec_eq(v_key_1003_, v_a_1000_);
if (v___x_1006_ == 0)
{
v_x_1001_ = v_tail_1005_;
goto _start;
}
else
{
lean_object* v___x_1008_; 
lean_inc(v_value_1004_);
v___x_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1008_, 0, v_value_1004_);
return v___x_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1009_, lean_object* v_x_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1009_, v_x_1010_);
lean_dec(v_x_1010_);
lean_dec(v_a_1009_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_buckets_1014_; lean_object* v___x_1015_; uint64_t v___x_1016_; uint64_t v___x_1017_; uint64_t v___x_1018_; uint64_t v_fold_1019_; uint64_t v___x_1020_; uint64_t v___x_1021_; uint64_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; size_t v___x_1025_; size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_buckets_1014_ = lean_ctor_get(v_m_1012_, 1);
v___x_1015_ = lean_array_get_size(v_buckets_1014_);
v___x_1016_ = lean_uint64_of_nat(v_a_1013_);
v___x_1017_ = 32ULL;
v___x_1018_ = lean_uint64_shift_right(v___x_1016_, v___x_1017_);
v_fold_1019_ = lean_uint64_xor(v___x_1016_, v___x_1018_);
v___x_1020_ = 16ULL;
v___x_1021_ = lean_uint64_shift_right(v_fold_1019_, v___x_1020_);
v___x_1022_ = lean_uint64_xor(v_fold_1019_, v___x_1021_);
v___x_1023_ = lean_uint64_to_usize(v___x_1022_);
v___x_1024_ = lean_usize_of_nat(v___x_1015_);
v___x_1025_ = ((size_t)1ULL);
v___x_1026_ = lean_usize_sub(v___x_1024_, v___x_1025_);
v___x_1027_ = lean_usize_land(v___x_1023_, v___x_1026_);
v___x_1028_ = lean_array_uget_borrowed(v_buckets_1014_, v___x_1027_);
v___x_1029_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1013_, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_m_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1033_, lean_object* v_b_1034_, lean_object* v_x_1035_){
_start:
{
if (lean_obj_tag(v_x_1035_) == 0)
{
lean_dec(v_b_1034_);
lean_dec(v_a_1033_);
return v_x_1035_;
}
else
{
lean_object* v_key_1036_; lean_object* v_value_1037_; lean_object* v_tail_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1050_; 
v_key_1036_ = lean_ctor_get(v_x_1035_, 0);
v_value_1037_ = lean_ctor_get(v_x_1035_, 1);
v_tail_1038_ = lean_ctor_get(v_x_1035_, 2);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_x_1035_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1040_ = v_x_1035_;
v_isShared_1041_ = v_isSharedCheck_1050_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_tail_1038_);
lean_inc(v_value_1037_);
lean_inc(v_key_1036_);
lean_dec(v_x_1035_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1050_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_nat_dec_eq(v_key_1036_, v_a_1033_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1033_, v_b_1034_, v_tail_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 2, v___x_1043_);
v___x_1045_ = v___x_1040_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_key_1036_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_value_1037_);
lean_ctor_set(v_reuseFailAlloc_1046_, 2, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
else
{
lean_object* v___x_1048_; 
lean_dec(v_value_1037_);
lean_dec(v_key_1036_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v_b_1034_);
lean_ctor_set(v___x_1040_, 0, v_a_1033_);
v___x_1048_ = v___x_1040_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1033_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_b_1034_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_tail_1038_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1051_, lean_object* v_a_1052_, lean_object* v_b_1053_){
_start:
{
lean_object* v_size_1054_; lean_object* v_buckets_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1098_; 
v_size_1054_ = lean_ctor_get(v_m_1051_, 0);
v_buckets_1055_ = lean_ctor_get(v_m_1051_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_m_1051_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1057_ = v_m_1051_;
v_isShared_1058_ = v_isSharedCheck_1098_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_buckets_1055_);
lean_inc(v_size_1054_);
lean_dec(v_m_1051_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1098_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; uint64_t v___x_1060_; uint64_t v___x_1061_; uint64_t v___x_1062_; uint64_t v_fold_1063_; uint64_t v___x_1064_; uint64_t v___x_1065_; uint64_t v___x_1066_; size_t v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; lean_object* v_bkt_1072_; uint8_t v___x_1073_; 
v___x_1059_ = lean_array_get_size(v_buckets_1055_);
v___x_1060_ = lean_uint64_of_nat(v_a_1052_);
v___x_1061_ = 32ULL;
v___x_1062_ = lean_uint64_shift_right(v___x_1060_, v___x_1061_);
v_fold_1063_ = lean_uint64_xor(v___x_1060_, v___x_1062_);
v___x_1064_ = 16ULL;
v___x_1065_ = lean_uint64_shift_right(v_fold_1063_, v___x_1064_);
v___x_1066_ = lean_uint64_xor(v_fold_1063_, v___x_1065_);
v___x_1067_ = lean_uint64_to_usize(v___x_1066_);
v___x_1068_ = lean_usize_of_nat(v___x_1059_);
v___x_1069_ = ((size_t)1ULL);
v___x_1070_ = lean_usize_sub(v___x_1068_, v___x_1069_);
v___x_1071_ = lean_usize_land(v___x_1067_, v___x_1070_);
v_bkt_1072_ = lean_array_uget_borrowed(v_buckets_1055_, v___x_1071_);
v___x_1073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1052_, v_bkt_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v_size_x27_1075_; lean_object* v___x_1076_; lean_object* v_buckets_x27_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1074_ = lean_unsigned_to_nat(1u);
v_size_x27_1075_ = lean_nat_add(v_size_1054_, v___x_1074_);
lean_dec(v_size_1054_);
lean_inc(v_bkt_1072_);
v___x_1076_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1076_, 0, v_a_1052_);
lean_ctor_set(v___x_1076_, 1, v_b_1053_);
lean_ctor_set(v___x_1076_, 2, v_bkt_1072_);
v_buckets_x27_1077_ = lean_array_uset(v_buckets_1055_, v___x_1071_, v___x_1076_);
v___x_1078_ = lean_unsigned_to_nat(4u);
v___x_1079_ = lean_nat_mul(v_size_x27_1075_, v___x_1078_);
v___x_1080_ = lean_unsigned_to_nat(3u);
v___x_1081_ = lean_nat_div(v___x_1079_, v___x_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_array_get_size(v_buckets_x27_1077_);
v___x_1083_ = lean_nat_dec_le(v___x_1081_, v___x_1082_);
lean_dec(v___x_1081_);
if (v___x_1083_ == 0)
{
lean_object* v_val_1084_; lean_object* v___x_1086_; 
v_val_1084_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1077_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v_val_1084_);
lean_ctor_set(v___x_1057_, 0, v_size_x27_1075_);
v___x_1086_ = v___x_1057_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_size_x27_1075_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_val_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
else
{
lean_object* v___x_1089_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v_buckets_x27_1077_);
lean_ctor_set(v___x_1057_, 0, v_size_x27_1075_);
v___x_1089_ = v___x_1057_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_size_x27_1075_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_buckets_x27_1077_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
else
{
lean_object* v___x_1091_; lean_object* v_buckets_x27_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
lean_inc(v_bkt_1072_);
v___x_1091_ = lean_box(0);
v_buckets_x27_1092_ = lean_array_uset(v_buckets_1055_, v___x_1071_, v___x_1091_);
v___x_1093_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1052_, v_b_1053_, v_bkt_1072_);
v___x_1094_ = lean_array_uset(v_buckets_x27_1092_, v___x_1071_, v___x_1093_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v___x_1094_);
v___x_1096_ = v___x_1057_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_size_1054_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
if (lean_obj_tag(v_x_1101_) == 0)
{
return v_x_1100_;
}
else
{
lean_object* v_key_1102_; lean_object* v_value_1103_; lean_object* v_tail_1104_; lean_object* v___y_1106_; lean_object* v___x_1109_; 
v_key_1102_ = lean_ctor_get(v_x_1101_, 0);
lean_inc(v_key_1102_);
v_value_1103_ = lean_ctor_get(v_x_1101_, 1);
lean_inc(v_value_1103_);
v_tail_1104_ = lean_ctor_get(v_x_1101_, 2);
lean_inc(v_tail_1104_);
lean_dec_ref_known(v_x_1101_, 3);
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1099_, v_key_1102_);
if (lean_obj_tag(v___x_1109_) == 1)
{
lean_object* v_val_1110_; uint8_t v___x_1111_; 
v_val_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_val_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = lean_nat_dec_le(v_value_1103_, v_val_1110_);
if (v___x_1111_ == 0)
{
lean_dec(v_value_1103_);
v___y_1106_ = v_val_1110_;
goto v___jp_1105_;
}
else
{
lean_dec(v_val_1110_);
v___y_1106_ = v_value_1103_;
goto v___jp_1105_;
}
}
else
{
lean_dec(v___x_1109_);
lean_dec(v_value_1103_);
lean_dec(v_key_1102_);
v_x_1101_ = v_tail_1104_;
goto _start;
}
v___jp_1105_:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1100_, v_key_1102_, v___y_1106_);
v_x_1100_ = v___x_1107_;
v_x_1101_ = v_tail_1104_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1113_, v_x_1114_, v_x_1115_);
lean_dec_ref(v_snd_1113_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1117_, lean_object* v_as_1118_, size_t v_i_1119_, size_t v_stop_1120_, lean_object* v_b_1121_){
_start:
{
uint8_t v___x_1122_; 
v___x_1122_ = lean_usize_dec_eq(v_i_1119_, v_stop_1120_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; size_t v___x_1125_; size_t v___x_1126_; 
v___x_1123_ = lean_array_uget_borrowed(v_as_1118_, v_i_1119_);
lean_inc(v___x_1123_);
v___x_1124_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1117_, v_b_1121_, v___x_1123_);
v___x_1125_ = ((size_t)1ULL);
v___x_1126_ = lean_usize_add(v_i_1119_, v___x_1125_);
v_i_1119_ = v___x_1126_;
v_b_1121_ = v___x_1124_;
goto _start;
}
else
{
return v_b_1121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1128_, lean_object* v_as_1129_, lean_object* v_i_1130_, lean_object* v_stop_1131_, lean_object* v_b_1132_){
_start:
{
size_t v_i_boxed_1133_; size_t v_stop_boxed_1134_; lean_object* v_res_1135_; 
v_i_boxed_1133_ = lean_unbox_usize(v_i_1130_);
lean_dec(v_i_1130_);
v_stop_boxed_1134_ = lean_unbox_usize(v_stop_1131_);
lean_dec(v_stop_1131_);
v_res_1135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1128_, v_as_1129_, v_i_boxed_1133_, v_stop_boxed_1134_, v_b_1132_);
lean_dec_ref(v_as_1129_);
lean_dec_ref(v_snd_1128_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1136_, lean_object* v_a_1137_, lean_object* v_x_1138_){
_start:
{
if (lean_obj_tag(v_x_1138_) == 0)
{
lean_dec(v_a_1137_);
return v_x_1138_;
}
else
{
lean_object* v_key_1139_; lean_object* v_value_1140_; lean_object* v_tail_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1154_; 
v_key_1139_ = lean_ctor_get(v_x_1138_, 0);
v_value_1140_ = lean_ctor_get(v_x_1138_, 1);
v_tail_1141_ = lean_ctor_get(v_x_1138_, 2);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_x_1138_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1143_ = v_x_1138_;
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_tail_1141_);
lean_inc(v_value_1140_);
lean_inc(v_key_1139_);
lean_dec(v_x_1138_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_nat_dec_eq(v_key_1139_, v_a_1137_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1136_, v_a_1137_, v_tail_1141_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 2, v___x_1146_);
v___x_1148_ = v___x_1143_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_key_1139_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_value_1140_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_dec(v_key_1139_);
v___x_1150_ = lean_nat_sub(v_value_1140_, v_commonCnt_1136_);
lean_dec(v_value_1140_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1150_);
lean_ctor_set(v___x_1143_, 0, v_a_1137_);
v___x_1152_ = v___x_1143_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1137_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_tail_1141_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1155_, lean_object* v_a_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1155_, v_a_1156_, v_x_1157_);
lean_dec(v_commonCnt_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1159_, lean_object* v_m_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_size_1162_; lean_object* v_buckets_1163_; lean_object* v___x_1164_; uint64_t v___x_1165_; uint64_t v___x_1166_; uint64_t v___x_1167_; uint64_t v_fold_1168_; uint64_t v___x_1169_; uint64_t v___x_1170_; uint64_t v___x_1171_; size_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; size_t v___x_1176_; lean_object* v_bucket_1177_; uint8_t v___x_1178_; 
v_size_1162_ = lean_ctor_get(v_m_1160_, 0);
v_buckets_1163_ = lean_ctor_get(v_m_1160_, 1);
v___x_1164_ = lean_array_get_size(v_buckets_1163_);
v___x_1165_ = lean_uint64_of_nat(v_a_1161_);
v___x_1166_ = 32ULL;
v___x_1167_ = lean_uint64_shift_right(v___x_1165_, v___x_1166_);
v_fold_1168_ = lean_uint64_xor(v___x_1165_, v___x_1167_);
v___x_1169_ = 16ULL;
v___x_1170_ = lean_uint64_shift_right(v_fold_1168_, v___x_1169_);
v___x_1171_ = lean_uint64_xor(v_fold_1168_, v___x_1170_);
v___x_1172_ = lean_uint64_to_usize(v___x_1171_);
v___x_1173_ = lean_usize_of_nat(v___x_1164_);
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_sub(v___x_1173_, v___x_1174_);
v___x_1176_ = lean_usize_land(v___x_1172_, v___x_1175_);
v_bucket_1177_ = lean_array_uget_borrowed(v_buckets_1163_, v___x_1176_);
v___x_1178_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1161_, v_bucket_1177_);
if (v___x_1178_ == 0)
{
lean_dec(v_a_1161_);
return v_m_1160_;
}
else
{
lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1189_; 
lean_inc(v_bucket_1177_);
lean_inc_ref(v_buckets_1163_);
lean_inc(v_size_1162_);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_m_1160_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; lean_object* v_unused_1191_; 
v_unused_1190_ = lean_ctor_get(v_m_1160_, 1);
lean_dec(v_unused_1190_);
v_unused_1191_ = lean_ctor_get(v_m_1160_, 0);
lean_dec(v_unused_1191_);
v___x_1180_ = v_m_1160_;
v_isShared_1181_ = v_isSharedCheck_1189_;
goto v_resetjp_1179_;
}
else
{
lean_dec(v_m_1160_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1189_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v_buckets_1183_; lean_object* v_bucket_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1182_ = lean_box(0);
v_buckets_1183_ = lean_array_uset(v_buckets_1163_, v___x_1176_, v___x_1182_);
v_bucket_1184_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1159_, v_a_1161_, v_bucket_1177_);
v___x_1185_ = lean_array_uset(v_buckets_1183_, v___x_1176_, v_bucket_1184_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1185_);
v___x_1187_ = v___x_1180_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_size_1162_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1192_, lean_object* v_m_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1192_, v_m_1193_, v_a_1194_);
lean_dec(v_commonCnt_1192_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
if (lean_obj_tag(v_x_1197_) == 0)
{
return v_x_1196_;
}
else
{
lean_object* v_key_1198_; lean_object* v_value_1199_; lean_object* v_tail_1200_; lean_object* v___x_1201_; 
v_key_1198_ = lean_ctor_get(v_x_1197_, 0);
lean_inc(v_key_1198_);
v_value_1199_ = lean_ctor_get(v_x_1197_, 1);
lean_inc(v_value_1199_);
v_tail_1200_ = lean_ctor_get(v_x_1197_, 2);
lean_inc(v_tail_1200_);
lean_dec_ref_known(v_x_1197_, 3);
v___x_1201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1199_, v_x_1196_, v_key_1198_);
lean_dec(v_value_1199_);
v_x_1196_ = v___x_1201_;
v_x_1197_ = v_tail_1200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1203_, lean_object* v_x_1204_){
_start:
{
if (lean_obj_tag(v_x_1204_) == 0)
{
return v_x_1203_;
}
else
{
lean_object* v_key_1205_; lean_object* v_value_1206_; lean_object* v_tail_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_key_1205_ = lean_ctor_get(v_x_1204_, 0);
lean_inc(v_key_1205_);
v_value_1206_ = lean_ctor_get(v_x_1204_, 1);
lean_inc(v_value_1206_);
v_tail_1207_ = lean_ctor_get(v_x_1204_, 2);
lean_inc(v_tail_1207_);
lean_dec_ref_known(v_x_1204_, 3);
v___x_1208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1206_, v_x_1203_, v_key_1205_);
lean_dec(v_value_1206_);
v___x_1209_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1208_, v_tail_1207_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1210_, size_t v_i_1211_, size_t v_stop_1212_, lean_object* v_b_1213_){
_start:
{
uint8_t v___x_1214_; 
v___x_1214_ = lean_usize_dec_eq(v_i_1211_, v_stop_1212_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; lean_object* v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; 
v___x_1215_ = lean_array_uget_borrowed(v_as_1210_, v_i_1211_);
lean_inc(v___x_1215_);
v___x_1216_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(v_b_1213_, v___x_1215_);
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1211_, v___x_1217_);
v_i_1211_ = v___x_1218_;
v_b_1213_ = v___x_1216_;
goto _start;
}
else
{
return v_b_1213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1220_, lean_object* v_i_1221_, lean_object* v_stop_1222_, lean_object* v_b_1223_){
_start:
{
size_t v_i_boxed_1224_; size_t v_stop_boxed_1225_; lean_object* v_res_1226_; 
v_i_boxed_1224_ = lean_unbox_usize(v_i_1221_);
lean_dec(v_i_1221_);
v_stop_boxed_1225_ = lean_unbox_usize(v_stop_1222_);
lean_dec(v_stop_1222_);
v_res_1226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_as_1220_, v_i_boxed_1224_, v_stop_boxed_1225_, v_b_1223_);
lean_dec_ref(v_as_1220_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1227_, lean_object* v_y_1228_, lean_object* v_a_1229_){
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
v___x_1258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1249_, v___x_1256_, v___x_1257_, v___y_1250_);
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
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1249_, v___x_1259_, v___x_1260_, v___y_1250_);
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
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1266_, v___x_1271_, v___x_1272_, v___y_1263_);
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
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1266_, v___x_1274_, v___x_1275_, v___y_1263_);
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
v___x_1287_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1288_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
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
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1285_, v_buckets_1284_, v___x_1292_, v___x_1293_, v___x_1288_);
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
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1285_, v_buckets_1284_, v___x_1295_, v___x_1296_, v___x_1288_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1299_, lean_object* v_y_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1299_, v_y_1300_, v_a_1301_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object* v_x_1304_, lean_object* v_y_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1304_, v_y_1305_, v_a_1306_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1313_, lean_object* v_y_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(v_x_1313_, v_y_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1322_, lean_object* v_m_1323_, lean_object* v_a_1324_, lean_object* v_b_1325_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1323_, v_a_1324_, v_b_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1327_, lean_object* v_m_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1328_, v_a_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1331_, lean_object* v_m_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1331_, v_m_1332_, v_a_1333_);
lean_dec(v_a_1333_);
lean_dec_ref(v_m_1332_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1335_, lean_object* v_a_1336_, lean_object* v_b_1337_, lean_object* v_x_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1336_, v_b_1337_, v_x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1340_, lean_object* v_a_1341_, lean_object* v_x_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1341_, v_x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1344_, lean_object* v_a_1345_, lean_object* v_x_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1344_, v_a_1345_, v_x_1346_);
lean_dec(v_x_1346_);
lean_dec(v_a_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1348_, lean_object* v_x_1349_){
_start:
{
if (lean_obj_tag(v_x_1349_) == 0)
{
return v_x_1348_;
}
else
{
lean_object* v_key_1350_; lean_object* v_value_1351_; lean_object* v_tail_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_key_1350_ = lean_ctor_get(v_x_1349_, 0);
v_value_1351_ = lean_ctor_get(v_x_1349_, 1);
v_tail_1352_ = lean_ctor_get(v_x_1349_, 2);
lean_inc(v_value_1351_);
lean_inc(v_key_1350_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_key_1350_);
lean_ctor_set(v___x_1353_, 1, v_value_1351_);
v___x_1354_ = lean_array_push(v_x_1348_, v___x_1353_);
v_x_1348_ = v___x_1354_;
v_x_1349_ = v_tail_1352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1356_, lean_object* v_x_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1356_, v_x_1357_);
lean_dec(v_x_1357_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1359_, size_t v_i_1360_, size_t v_stop_1361_, lean_object* v_b_1362_){
_start:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_usize_dec_eq(v_i_1360_, v_stop_1361_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; size_t v___x_1366_; size_t v___x_1367_; 
v___x_1364_ = lean_array_uget_borrowed(v_as_1359_, v_i_1360_);
v___x_1365_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1362_, v___x_1364_);
v___x_1366_ = ((size_t)1ULL);
v___x_1367_ = lean_usize_add(v_i_1360_, v___x_1366_);
v_i_1360_ = v___x_1367_;
v_b_1362_ = v___x_1365_;
goto _start;
}
else
{
return v_b_1362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1369_, lean_object* v_i_1370_, lean_object* v_stop_1371_, lean_object* v_b_1372_){
_start:
{
size_t v_i_boxed_1373_; size_t v_stop_boxed_1374_; lean_object* v_res_1375_; 
v_i_boxed_1373_ = lean_unbox_usize(v_i_1370_);
lean_dec(v_i_1370_);
v_stop_boxed_1374_ = lean_unbox_usize(v_stop_1371_);
lean_dec(v_stop_1371_);
v_res_1375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1369_, v_i_boxed_1373_, v_stop_boxed_1374_, v_b_1372_);
lean_dec_ref(v_as_1369_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1376_, lean_object* v___x_1377_, lean_object* v_op_1378_, lean_object* v_a_1379_, lean_object* v_b_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___y_1384_; uint8_t v___x_1388_; 
v___x_1388_ = lean_nat_dec_lt(v_a_1379_, v_upperBound_1376_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec(v_a_1379_);
lean_dec_ref(v_op_1378_);
lean_dec_ref(v___x_1377_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_b_1380_);
lean_ctor_set(v___x_1389_, 1, v___y_1381_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
else
{
if (lean_obj_tag(v_b_1380_) == 0)
{
lean_object* v___x_1391_; 
lean_inc_ref(v___x_1377_);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1377_);
v___y_1384_ = v___x_1391_;
goto v___jp_1383_;
}
else
{
lean_object* v_val_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1401_; 
v_val_1392_ = lean_ctor_get(v_b_1380_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_b_1380_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1394_ = v_b_1380_;
v_isShared_1395_ = v_isSharedCheck_1401_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_val_1392_);
lean_dec(v_b_1380_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1401_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
lean_inc_ref(v_op_1378_);
v___x_1396_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_1378_);
lean_inc_ref(v___x_1377_);
v___x_1397_ = l_Lean_mkAppB(v___x_1396_, v_val_1392_, v___x_1377_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1397_);
v___x_1399_ = v___x_1394_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
v___y_1384_ = v___x_1399_;
goto v___jp_1383_;
}
}
}
}
v___jp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_unsigned_to_nat(1u);
v___x_1386_ = lean_nat_add(v_a_1379_, v___x_1385_);
lean_dec(v_a_1379_);
v_a_1379_ = v___x_1386_;
v_b_1380_ = v___y_1384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1402_, lean_object* v___x_1403_, lean_object* v_op_1404_, lean_object* v_a_1405_, lean_object* v_b_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1402_, v___x_1403_, v_op_1404_, v_a_1405_, v_b_1406_, v___y_1407_);
lean_dec(v_upperBound_1402_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1410_, lean_object* v_as_1411_, size_t v_sz_1412_, size_t v_i_1413_, lean_object* v_b_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_usize_dec_lt(v_i_1413_, v_sz_1412_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v_op_1410_);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v_b_1414_);
lean_ctor_set(v___x_1422_, 1, v___y_1415_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
else
{
lean_object* v_a_1424_; lean_object* v_fst_1425_; lean_object* v_snd_1426_; lean_object* v_varToExpr_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v_a_1424_ = lean_array_uget_borrowed(v_as_1411_, v_i_1413_);
v_fst_1425_ = lean_ctor_get(v_a_1424_, 0);
v_snd_1426_ = lean_ctor_get(v_a_1424_, 1);
v_varToExpr_1427_ = lean_ctor_get(v___y_1415_, 2);
v___x_1428_ = l_Lean_instInhabitedExpr;
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_array_get(v___x_1428_, v_varToExpr_1427_, v_fst_1425_);
lean_inc_ref(v_op_1410_);
v___x_1431_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1426_, v___x_1430_, v_op_1410_, v___x_1429_, v_b_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v_fst_1433_; lean_object* v_snd_1434_; size_t v___x_1435_; size_t v___x_1436_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v_fst_1433_ = lean_ctor_get(v_a_1432_, 0);
lean_inc(v_fst_1433_);
v_snd_1434_ = lean_ctor_get(v_a_1432_, 1);
lean_inc(v_snd_1434_);
lean_dec(v_a_1432_);
v___x_1435_ = ((size_t)1ULL);
v___x_1436_ = lean_usize_add(v_i_1413_, v___x_1435_);
v_i_1413_ = v___x_1436_;
v_b_1414_ = v_fst_1433_;
v___y_1415_ = v_snd_1434_;
goto _start;
}
else
{
lean_dec_ref(v_op_1410_);
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1438_, lean_object* v_as_1439_, lean_object* v_sz_1440_, lean_object* v_i_1441_, lean_object* v_b_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
size_t v_sz_boxed_1449_; size_t v_i_boxed_1450_; lean_object* v_res_1451_; 
v_sz_boxed_1449_ = lean_unbox_usize(v_sz_1440_);
lean_dec(v_sz_1440_);
v_i_boxed_1450_ = lean_unbox_usize(v_i_1441_);
lean_dec(v_i_1441_);
v_res_1451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1438_, v_as_1439_, v_sz_boxed_1449_, v_i_boxed_1450_, v_b_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec_ref(v_as_1439_);
return v_res_1451_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1452_, lean_object* v_x2_1453_){
_start:
{
lean_object* v_fst_1454_; lean_object* v_fst_1455_; uint8_t v___x_1456_; 
v_fst_1454_ = lean_ctor_get(v_x1_1452_, 0);
v_fst_1455_ = lean_ctor_get(v_x2_1453_, 0);
v___x_1456_ = lean_nat_dec_lt(v_fst_1454_, v_fst_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1457_, lean_object* v_x2_1458_){
_start:
{
uint8_t v_res_1459_; lean_object* v_r_1460_; 
v_res_1459_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1457_, v_x2_1458_);
lean_dec_ref(v_x2_1458_);
lean_dec_ref(v_x1_1457_);
v_r_1460_ = lean_box(v_res_1459_);
return v_r_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object* v_hi_1461_, lean_object* v_pivot_1462_, lean_object* v_as_1463_, lean_object* v_i_1464_, lean_object* v_k_1465_){
_start:
{
uint8_t v___x_1466_; 
v___x_1466_ = lean_nat_dec_lt(v_k_1465_, v_hi_1461_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec(v_k_1465_);
v___x_1467_ = lean_array_fswap(v_as_1463_, v_i_1464_, v_hi_1461_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_i_1464_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
return v___x_1468_;
}
else
{
lean_object* v___x_1469_; lean_object* v_fst_1470_; lean_object* v_fst_1471_; uint8_t v___x_1472_; 
v___x_1469_ = lean_array_fget_borrowed(v_as_1463_, v_k_1465_);
v_fst_1470_ = lean_ctor_get(v___x_1469_, 0);
v_fst_1471_ = lean_ctor_get(v_pivot_1462_, 0);
v___x_1472_ = lean_nat_dec_lt(v_fst_1470_, v_fst_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v_k_1465_, v___x_1473_);
lean_dec(v_k_1465_);
v_k_1465_ = v___x_1474_;
goto _start;
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1476_ = lean_array_fswap(v_as_1463_, v_i_1464_, v_k_1465_);
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_nat_add(v_i_1464_, v___x_1477_);
lean_dec(v_i_1464_);
v___x_1479_ = lean_nat_add(v_k_1465_, v___x_1477_);
lean_dec(v_k_1465_);
v_as_1463_ = v___x_1476_;
v_i_1464_ = v___x_1478_;
v_k_1465_ = v___x_1479_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object* v_hi_1481_, lean_object* v_pivot_1482_, lean_object* v_as_1483_, lean_object* v_i_1484_, lean_object* v_k_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1481_, v_pivot_1482_, v_as_1483_, v_i_1484_, v_k_1485_);
lean_dec_ref(v_pivot_1482_);
lean_dec(v_hi_1481_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_n_1487_, lean_object* v_as_1488_, lean_object* v_lo_1489_, lean_object* v_hi_1490_){
_start:
{
lean_object* v___y_1492_; uint8_t v___x_1502_; 
v___x_1502_ = lean_nat_dec_lt(v_lo_1489_, v_hi_1490_);
if (v___x_1502_ == 0)
{
lean_dec(v_lo_1489_);
return v_as_1488_;
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v_mid_1505_; lean_object* v___y_1507_; lean_object* v___y_1513_; lean_object* v___x_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1503_ = lean_nat_add(v_lo_1489_, v_hi_1490_);
v___x_1504_ = lean_unsigned_to_nat(1u);
v_mid_1505_ = lean_nat_shiftr(v___x_1503_, v___x_1504_);
lean_dec(v___x_1503_);
v___x_1518_ = lean_array_fget_borrowed(v_as_1488_, v_mid_1505_);
v___x_1519_ = lean_array_fget_borrowed(v_as_1488_, v_lo_1489_);
v___x_1520_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1518_, v___x_1519_);
if (v___x_1520_ == 0)
{
v___y_1513_ = v_as_1488_;
goto v___jp_1512_;
}
else
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_array_fswap(v_as_1488_, v_lo_1489_, v_mid_1505_);
v___y_1513_ = v___x_1521_;
goto v___jp_1512_;
}
v___jp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1508_ = lean_array_fget_borrowed(v___y_1507_, v_mid_1505_);
v___x_1509_ = lean_array_fget_borrowed(v___y_1507_, v_hi_1490_);
v___x_1510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1508_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_dec(v_mid_1505_);
v___y_1492_ = v___y_1507_;
goto v___jp_1491_;
}
else
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_array_fswap(v___y_1507_, v_mid_1505_, v_hi_1490_);
lean_dec(v_mid_1505_);
v___y_1492_ = v___x_1511_;
goto v___jp_1491_;
}
}
v___jp_1512_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1514_ = lean_array_fget_borrowed(v___y_1513_, v_hi_1490_);
v___x_1515_ = lean_array_fget_borrowed(v___y_1513_, v_lo_1489_);
v___x_1516_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1514_, v___x_1515_);
if (v___x_1516_ == 0)
{
v___y_1507_ = v___y_1513_;
goto v___jp_1506_;
}
else
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_array_fswap(v___y_1513_, v_lo_1489_, v_hi_1490_);
v___y_1507_ = v___x_1517_;
goto v___jp_1506_;
}
}
}
v___jp_1491_:
{
lean_object* v_pivot_1493_; lean_object* v___x_1494_; lean_object* v_fst_1495_; lean_object* v_snd_1496_; uint8_t v___x_1497_; 
v_pivot_1493_ = lean_array_fget(v___y_1492_, v_hi_1490_);
lean_inc_n(v_lo_1489_, 2);
v___x_1494_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1490_, v_pivot_1493_, v___y_1492_, v_lo_1489_, v_lo_1489_);
lean_dec(v_pivot_1493_);
v_fst_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_fst_1495_);
v_snd_1496_ = lean_ctor_get(v___x_1494_, 1);
lean_inc(v_snd_1496_);
lean_dec_ref(v___x_1494_);
v___x_1497_ = lean_nat_dec_le(v_hi_1490_, v_fst_1495_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1487_, v_snd_1496_, v_lo_1489_, v_fst_1495_);
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_add(v_fst_1495_, v___x_1499_);
lean_dec(v_fst_1495_);
v_as_1488_ = v___x_1498_;
v_lo_1489_ = v___x_1500_;
goto _start;
}
else
{
lean_dec(v_fst_1495_);
lean_dec(v_lo_1489_);
return v_snd_1496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_n_1522_, lean_object* v_as_1523_, lean_object* v_lo_1524_, lean_object* v_hi_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1522_, v_as_1523_, v_lo_1524_, v_hi_1525_);
lean_dec(v_hi_1525_);
lean_dec(v_n_1522_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1527_, lean_object* v_op_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
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
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1562_, v___x_1568_, v___x_1569_, v___x_1563_);
v___y_1554_ = v___x_1570_;
goto v___jp_1553_;
}
}
else
{
size_t v___x_1571_; size_t v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = ((size_t)0ULL);
v___x_1572_ = lean_usize_of_nat(v___x_1565_);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1562_, v___x_1571_, v___x_1572_, v___x_1563_);
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
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1528_, v___y_1536_, v_sz_1538_, v___x_1539_, v_acc_1537_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec_ref(v___y_1536_);
return v___x_1540_;
}
v___jp_1541_:
{
lean_object* v___x_1546_; 
v___x_1546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1544_, v___y_1543_, v___y_1542_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec(v___y_1544_);
v___y_1536_ = v___x_1546_;
goto v___jp_1535_;
}
v___jp_1547_:
{
uint8_t v___x_1552_; 
v___x_1552_ = lean_nat_dec_le(v___y_1551_, v___y_1550_);
if (v___x_1552_ == 0)
{
lean_dec(v___y_1550_);
lean_inc(v___y_1551_);
v___y_1542_ = v___y_1551_;
v___y_1543_ = v___y_1548_;
v___y_1544_ = v___y_1549_;
v___y_1545_ = v___y_1551_;
goto v___jp_1541_;
}
else
{
v___y_1542_ = v___y_1551_;
v___y_1543_ = v___y_1548_;
v___y_1544_ = v___y_1549_;
v___y_1545_ = v___y_1550_;
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
v___y_1549_ = v___x_1555_;
v___y_1550_ = v___x_1559_;
v___y_1551_ = v___x_1559_;
goto v___jp_1547_;
}
else
{
v___y_1548_ = v___y_1554_;
v___y_1549_ = v___x_1555_;
v___y_1550_ = v___x_1559_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1574_, lean_object* v_op_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_coeff_1574_, v_op_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec_ref(v_coeff_1574_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1583_, lean_object* v___x_1584_, lean_object* v_op_1585_, lean_object* v_inst_1586_, lean_object* v_R_1587_, lean_object* v_a_1588_, lean_object* v_b_1589_, lean_object* v_c_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1583_, v___x_1584_, v_op_1585_, v_a_1588_, v_b_1589_, v___y_1591_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1598_, lean_object* v___x_1599_, lean_object* v_op_1600_, lean_object* v_inst_1601_, lean_object* v_R_1602_, lean_object* v_a_1603_, lean_object* v_b_1604_, lean_object* v_c_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1598_, v___x_1599_, v_op_1600_, v_inst_1601_, v_R_1602_, v_a_1603_, v_b_1604_, v_c_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v_upperBound_1598_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1613_, lean_object* v_as_1614_, lean_object* v_lo_1615_, lean_object* v_hi_1616_, lean_object* v_w_1617_, lean_object* v_hlo_1618_, lean_object* v_hhi_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1613_, v_as_1614_, v_lo_1615_, v_hi_1616_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1621_, lean_object* v_as_1622_, lean_object* v_lo_1623_, lean_object* v_hi_1624_, lean_object* v_w_1625_, lean_object* v_hlo_1626_, lean_object* v_hhi_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1621_, v_as_1622_, v_lo_1623_, v_hi_1624_, v_w_1625_, v_hlo_1626_, v_hhi_1627_);
lean_dec(v_hi_1624_);
lean_dec(v_n_1621_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object* v_n_1629_, lean_object* v_lo_1630_, lean_object* v_hi_1631_, lean_object* v_hhi_1632_, lean_object* v_pivot_1633_, lean_object* v_as_1634_, lean_object* v_i_1635_, lean_object* v_k_1636_, lean_object* v_ilo_1637_, lean_object* v_ik_1638_, lean_object* v_w_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1631_, v_pivot_1633_, v_as_1634_, v_i_1635_, v_k_1636_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object* v_n_1641_, lean_object* v_lo_1642_, lean_object* v_hi_1643_, lean_object* v_hhi_1644_, lean_object* v_pivot_1645_, lean_object* v_as_1646_, lean_object* v_i_1647_, lean_object* v_k_1648_, lean_object* v_ilo_1649_, lean_object* v_ik_1650_, lean_object* v_w_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_n_1641_, v_lo_1642_, v_hi_1643_, v_hhi_1644_, v_pivot_1645_, v_as_1646_, v_i_1647_, v_k_1648_, v_ilo_1649_, v_ik_1650_, v_w_1651_);
lean_dec_ref(v_pivot_1645_);
lean_dec(v_hi_1643_);
lean_dec(v_lo_1642_);
lean_dec(v_n_1641_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1653_, lean_object* v___y_1654_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1678_, v___y_1679_);
lean_dec(v___y_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1682_, v___y_1684_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(v_e_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object* v_x_1696_, lean_object* v_y_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
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
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = l_Lean_Expr_mvarId_x21(v_a_1713_);
v___x_1715_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1714_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v___x_1716_; 
lean_dec_ref_known(v___x_1715_, 1);
v___x_1716_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1713_, v_a_1699_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1727_, lean_object* v_y_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v_x_1727_, v_y_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
return v_res_1734_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1738_ = ((size_t)5ULL);
v___x_1739_ = lean_unsigned_to_nat(0u);
v___x_1740_ = lean_unsigned_to_nat(32u);
v___x_1741_ = lean_mk_empty_array_with_capacity(v___x_1740_);
v___x_1742_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1743_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v___x_1741_);
lean_ctor_set(v___x_1743_, 2, v___x_1739_);
lean_ctor_set(v___x_1743_, 3, v___x_1739_);
lean_ctor_set_usize(v___x_1743_, 4, v___x_1738_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1744_){
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
v___x_1766_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1778_);
lean_dec(v___y_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1787_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1799_, lean_object* v_opt_1800_){
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
lean_dec_ref_known(v___x_1804_, 1);
if (lean_obj_tag(v_val_1806_) == 1)
{
uint8_t v_v_1807_; 
v_v_1807_ = lean_ctor_get_uint8(v_val_1806_, 0);
lean_dec_ref_known(v_val_1806_, 0);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1809_, lean_object* v_opt_1810_){
_start:
{
uint8_t v_res_1811_; lean_object* v_r_1812_; 
v_res_1811_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_1809_, v_opt_1810_);
lean_dec_ref(v_opt_1810_);
lean_dec_ref(v_opts_1809_);
v_r_1812_ = lean_box(v_res_1811_);
return v_r_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1813_, lean_object* v_____do__lift_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
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
v___x_1827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1832_, lean_object* v_____do__lift_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_1832_, v_____do__lift_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_mkAppB(v___x_1843_, v___y_1844_, v___y_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1847_, lean_object* v_lhs_1848_, lean_object* v_rhs_1849_, lean_object* v_P_1850_, uint8_t v___x_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; 
lean_inc_ref(v_lhs_1848_);
lean_inc_ref(v_val_1847_);
v___x_1858_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1847_, v_lhs_1848_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v_fst_1860_; lean_object* v_snd_1861_; lean_object* v___x_1862_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1858_, 1);
v_fst_1860_ = lean_ctor_get(v_a_1859_, 0);
lean_inc(v_fst_1860_);
v_snd_1861_ = lean_ctor_get(v_a_1859_, 1);
lean_inc(v_snd_1861_);
lean_dec(v_a_1859_);
lean_inc_ref(v_rhs_1849_);
lean_inc_ref(v_val_1847_);
v___x_1862_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1847_, v_rhs_1849_, v_snd_1861_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v_fst_1864_; lean_object* v_snd_1865_; lean_object* v___x_1866_; lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1957_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref_known(v___x_1862_, 1);
v_fst_1864_ = lean_ctor_get(v_a_1863_, 0);
lean_inc(v_fst_1864_);
v_snd_1865_ = lean_ctor_get(v_a_1863_, 1);
lean_inc(v_snd_1865_);
lean_dec(v_a_1863_);
v___x_1866_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_1860_, v_fst_1864_, v_snd_1865_);
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
v___x_1876_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_1873_, v_val_1847_, v_snd_1872_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec_ref(v_common_1873_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v_fst_1878_; lean_object* v_snd_1879_; lean_object* v___x_1880_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v_fst_1878_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_fst_1878_);
v_snd_1879_ = lean_ctor_get(v_a_1877_, 1);
lean_inc(v_snd_1879_);
lean_dec(v_a_1877_);
lean_inc_ref(v_val_1847_);
v___x_1880_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_1874_, v_val_1847_, v_snd_1879_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec_ref(v_x_1874_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_fst_1882_; lean_object* v_snd_1883_; lean_object* v___x_1884_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v_fst_1882_ = lean_ctor_get(v_a_1881_, 0);
lean_inc(v_fst_1882_);
v_snd_1883_ = lean_ctor_get(v_a_1881_, 1);
lean_inc(v_snd_1883_);
lean_dec(v_a_1881_);
lean_inc_ref(v_val_1847_);
v___x_1884_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_1875_, v_val_1847_, v_snd_1883_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec_ref(v_y_1875_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v_fst_1886_; lean_object* v_snd_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1932_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
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
v___x_1922_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_1847_);
v___f_1923_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_1923_, 0, v___x_1922_);
lean_inc(v_fst_1878_);
lean_inc_ref(v___f_1923_);
v___x_1929_ = l_Option_merge___redArg(v___f_1923_, v_fst_1878_, v_fst_1882_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v___x_1930_; 
lean_inc_ref(v_val_1847_);
v___x_1930_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1847_);
v___y_1925_ = v___x_1930_;
goto v___jp_1924_;
}
else
{
lean_object* v_val_1931_; 
v_val_1931_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_val_1931_);
lean_dec_ref_known(v___x_1929_, 1);
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
v___x_1896_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_1894_, v___x_1895_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
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
v___x_1927_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1847_);
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
lean_dec_ref_known(v___x_1926_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_1974_, lean_object* v_lhs_1975_, lean_object* v_rhs_1976_, lean_object* v_P_1977_, lean_object* v___x_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
uint8_t v___x_117948__boxed_1985_; lean_object* v_res_1986_; 
v___x_117948__boxed_1985_ = lean_unbox(v___x_1978_);
v_res_1986_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(v_val_1974_, v_lhs_1975_, v_rhs_1976_, v_P_1977_, v___x_117948__boxed_1985_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
return v_res_1986_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_1989_ = l_Lean_stringToMessageData(v___x_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(v_x_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object* v_val_2011_, lean_object* v_lhs_2012_, lean_object* v_rhs_2013_, lean_object* v_P_2014_, uint8_t v_hasTrace_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; 
lean_inc_ref(v_lhs_2012_);
lean_inc_ref(v_val_2011_);
v___x_2022_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2011_, v_lhs_2012_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v_fst_2024_; lean_object* v_snd_2025_; lean_object* v___x_2026_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v_fst_2024_ = lean_ctor_get(v_a_2023_, 0);
lean_inc(v_fst_2024_);
v_snd_2025_ = lean_ctor_get(v_a_2023_, 1);
lean_inc(v_snd_2025_);
lean_dec(v_a_2023_);
lean_inc_ref(v_rhs_2013_);
lean_inc_ref(v_val_2011_);
v___x_2026_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2011_, v_rhs_2013_, v_snd_2025_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v___x_2030_; lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2121_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v_fst_2028_ = lean_ctor_get(v_a_2027_, 0);
lean_inc(v_fst_2028_);
v_snd_2029_ = lean_ctor_get(v_a_2027_, 1);
lean_inc(v_snd_2029_);
lean_dec(v_a_2027_);
v___x_2030_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_2024_, v_fst_2028_, v_snd_2029_);
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
v___x_2040_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_2037_, v_val_2011_, v_snd_2036_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec_ref(v_common_2037_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v_fst_2042_; lean_object* v_snd_2043_; lean_object* v___x_2044_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v_fst_2042_ = lean_ctor_get(v_a_2041_, 0);
lean_inc(v_fst_2042_);
v_snd_2043_ = lean_ctor_get(v_a_2041_, 1);
lean_inc(v_snd_2043_);
lean_dec(v_a_2041_);
lean_inc_ref(v_val_2011_);
v___x_2044_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_2038_, v_val_2011_, v_snd_2043_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec_ref(v_x_2038_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v_fst_2046_; lean_object* v_snd_2047_; lean_object* v___x_2048_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
v_fst_2046_ = lean_ctor_get(v_a_2045_, 0);
lean_inc(v_fst_2046_);
v_snd_2047_ = lean_ctor_get(v_a_2045_, 1);
lean_inc(v_snd_2047_);
lean_dec(v_a_2045_);
lean_inc_ref(v_val_2011_);
v___x_2048_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_2039_, v_val_2011_, v_snd_2047_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec_ref(v_y_2039_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v_fst_2050_; lean_object* v_snd_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2096_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2048_, 1);
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
v___x_2086_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2011_);
v___f_2087_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2087_, 0, v___x_2086_);
lean_inc(v_fst_2042_);
lean_inc_ref(v___f_2087_);
v___x_2093_ = l_Option_merge___redArg(v___f_2087_, v_fst_2042_, v_fst_2046_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v___x_2094_; 
lean_inc_ref(v_val_2011_);
v___x_2094_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2011_);
v___y_2089_ = v___x_2094_;
goto v___jp_2088_;
}
else
{
lean_object* v_val_2095_; 
v_val_2095_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v___x_2093_, 1);
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
v___x_2060_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_2058_, v___x_2059_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
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
v___x_2091_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2011_);
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
lean_dec_ref_known(v___x_2090_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object* v_val_2138_, lean_object* v_lhs_2139_, lean_object* v_rhs_2140_, lean_object* v_P_2141_, lean_object* v_hasTrace_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
uint8_t v_hasTrace_boxed_2149_; lean_object* v_res_2150_; 
v_hasTrace_boxed_2149_ = lean_unbox(v_hasTrace_2142_);
v_res_2150_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(v_val_2138_, v_lhs_2139_, v_rhs_2140_, v_P_2141_, v_hasTrace_boxed_2149_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2151_, lean_object* v_msg_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_ref_2158_; lean_object* v___x_2159_; lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2204_; 
v_ref_2158_ = lean_ctor_get(v___y_2155_, 5);
v___x_2159_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
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
v___x_2183_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
v___x_2184_ = 0;
v___x_2185_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_2186_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2186_, 0, v_cls_2151_);
lean_ctor_set(v___x_2186_, 1, v___x_2182_);
lean_ctor_set(v___x_2186_, 2, v___x_2185_);
lean_ctor_set_float(v___x_2186_, sizeof(void*)*3, v___x_2183_);
lean_ctor_set_float(v___x_2186_, sizeof(void*)*3 + 8, v___x_2183_);
lean_ctor_set_uint8(v___x_2186_, sizeof(void*)*3 + 16, v___x_2184_);
v___x_2187_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2));
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2205_, lean_object* v_msg_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2205_, v_msg_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
return v_res_2212_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1));
v___x_2217_ = l_Lean_stringToMessageData(v___x_2216_);
return v___x_2217_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3));
v___x_2220_ = l_Lean_stringToMessageData(v___x_2219_);
return v___x_2220_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5));
v___x_2223_ = l_Lean_stringToMessageData(v___x_2222_);
return v___x_2223_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_unsigned_to_nat(16u);
v___x_2226_ = lean_mk_array(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7);
v___x_2228_ = lean_unsigned_to_nat(0u);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v___x_2227_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10));
v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12));
v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14));
v___x_2240_ = l_Lean_stringToMessageData(v___x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object* v_lhs_2241_, lean_object* v_rhs_2242_, lean_object* v___f_2243_, lean_object* v_cls_2244_, uint8_t v___x_2245_, lean_object* v_P_2246_, uint8_t v_hasTrace_2247_, lean_object* v_____r_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v___x_2266_; 
lean_inc_ref(v_lhs_2241_);
v___x_2266_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2241_);
if (lean_obj_tag(v___x_2266_) == 1)
{
lean_object* v_val_2267_; lean_object* v___x_2268_; 
v_val_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_val_2267_);
lean_dec_ref_known(v___x_2266_, 1);
lean_inc_ref(v_rhs_2242_);
v___x_2268_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2242_);
if (lean_obj_tag(v___x_2268_) == 1)
{
lean_object* v_val_2269_; uint8_t v___x_2308_; 
v_val_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_val_2269_);
lean_dec_ref_known(v___x_2268_, 1);
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
v___f_2313_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed), 11, 5);
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
v___x_2323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
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
v___x_2326_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11);
lean_inc(v_val_2267_);
v___x_2327_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2267_);
v___x_2328_ = l_Lean_MessageData_ofExpr(v___x_2327_);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2326_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13);
v___x_2331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2244_, v___x_2331_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_dec_ref_known(v___x_2332_, 1);
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
v___x_2319_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8);
v___x_2320_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2321_, 0, v_val_2267_);
lean_ctor_set(v___x_2321_, 1, v___x_2319_);
lean_ctor_set(v___x_2321_, 2, v___x_2320_);
v___x_2322_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2313_, v___x_2321_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
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
lean_dec_ref_known(v___x_2272_, 1);
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
v___x_2275_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2);
v___x_2276_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2267_);
v___x_2277_ = l_Lean_MessageData_ofExpr(v___x_2276_);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2275_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4);
v___x_2280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = l_Lean_indentExpr(v_lhs_2241_);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2269_);
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
v___x_2291_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2244_, v___x_2290_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_dec_ref_known(v___x_2291_, 1);
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
lean_dec_ref_known(v___x_2342_, 1);
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
v___x_2345_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2346_ = l_Lean_indentExpr(v_rhs_2242_);
v___x_2347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2244_, v___x_2347_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_dec_ref_known(v___x_2348_, 1);
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
lean_dec_ref_known(v___x_2366_, 1);
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
v___x_2369_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2370_ = l_Lean_indentExpr(v_lhs_2241_);
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2244_, v___x_2371_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_dec_ref_known(v___x_2372_, 1);
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
v___x_2258_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
return v___x_2259_;
}
v___jp_2260_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
v___jp_2263_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object* v_lhs_2389_, lean_object* v_rhs_2390_, lean_object* v___f_2391_, lean_object* v_cls_2392_, lean_object* v___x_2393_, lean_object* v_P_2394_, lean_object* v_hasTrace_2395_, lean_object* v_____r_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
uint8_t v___x_118658__boxed_2405_; uint8_t v_hasTrace_boxed_2406_; lean_object* v_res_2407_; 
v___x_118658__boxed_2405_ = lean_unbox(v___x_2393_);
v_hasTrace_boxed_2406_ = lean_unbox(v_hasTrace_2395_);
v_res_2407_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2389_, v_rhs_2390_, v___f_2391_, v_cls_2392_, v___x_118658__boxed_2405_, v_P_2394_, v_hasTrace_boxed_2406_, v_____r_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__8(lean_object* v_lhs_2408_, lean_object* v_rhs_2409_, lean_object* v_P_2410_, uint8_t v___x_2411_, lean_object* v_cls_2412_, lean_object* v___f_2413_, lean_object* v_____r_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___x_2432_; 
lean_inc_ref(v_lhs_2408_);
v___x_2432_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2408_);
if (lean_obj_tag(v___x_2432_) == 1)
{
lean_object* v_val_2433_; lean_object* v___x_2434_; 
v_val_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_val_2433_);
lean_dec_ref_known(v___x_2432_, 1);
lean_inc_ref(v_rhs_2409_);
v___x_2434_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2409_);
if (lean_obj_tag(v___x_2434_) == 1)
{
lean_object* v_val_2435_; lean_object* v___x_2436_; lean_object* v___f_2437_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; uint8_t v___x_2469_; 
v_val_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_val_2435_);
lean_dec_ref_known(v___x_2434_, 1);
v___x_2436_ = lean_box(v___x_2411_);
lean_inc_ref(v_rhs_2409_);
lean_inc_ref(v_lhs_2408_);
lean_inc(v_val_2433_);
v___f_2437_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 11, 5);
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
lean_dec_ref_known(v___x_2471_, 1);
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
v___x_2474_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2);
v___x_2475_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2433_);
v___x_2476_ = l_Lean_MessageData_ofExpr(v___x_2475_);
v___x_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2474_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4);
v___x_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = l_Lean_indentExpr(v_lhs_2408_);
v___x_2481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2435_);
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
v___x_2490_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2412_, v___x_2489_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_dec_ref_known(v___x_2490_, 1);
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
v___x_2443_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8);
v___x_2444_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2445_, 0, v_val_2433_);
lean_ctor_set(v___x_2445_, 1, v___x_2443_);
lean_ctor_set(v___x_2445_, 2, v___x_2444_);
v___x_2446_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2437_, v___x_2445_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
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
v___x_2451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
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
v___x_2454_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11);
lean_inc(v_val_2433_);
v___x_2455_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2433_);
v___x_2456_ = l_Lean_MessageData_ofExpr(v___x_2455_);
v___x_2457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2454_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2412_, v___x_2459_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_dec_ref_known(v___x_2460_, 1);
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
lean_dec_ref_known(v___x_2508_, 1);
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
v___x_2511_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2512_ = l_Lean_indentExpr(v_rhs_2409_);
v___x_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2412_, v___x_2513_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_dec_ref_known(v___x_2514_, 1);
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
lean_dec_ref_known(v___x_2532_, 1);
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
v___x_2535_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2536_ = l_Lean_indentExpr(v_lhs_2408_);
v___x_2537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2412_, v___x_2537_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_dec_ref_known(v___x_2538_, 1);
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
v___x_2424_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
v___jp_2426_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
return v___x_2428_;
}
v___jp_2429_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
return v___x_2431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__8___boxed(lean_object* v_lhs_2555_, lean_object* v_rhs_2556_, lean_object* v_P_2557_, lean_object* v___x_2558_, lean_object* v_cls_2559_, lean_object* v___f_2560_, lean_object* v_____r_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
uint8_t v___x_119014__boxed_2570_; lean_object* v_res_2571_; 
v___x_119014__boxed_2570_ = lean_unbox(v___x_2558_);
v_res_2571_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__8(v_lhs_2555_, v_rhs_2556_, v_P_2557_, v___x_119014__boxed_2570_, v_cls_2559_, v___f_2560_, v_____r_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_x_2572_){
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_x_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_2590_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2593_, lean_object* v_opt_2594_){
_start:
{
lean_object* v_name_2595_; lean_object* v_defValue_2596_; lean_object* v_map_2597_; lean_object* v___x_2598_; 
v_name_2595_ = lean_ctor_get(v_opt_2594_, 0);
v_defValue_2596_ = lean_ctor_get(v_opt_2594_, 1);
v_map_2597_ = lean_ctor_get(v_opts_2593_, 0);
v___x_2598_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2597_, v_name_2595_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_inc(v_defValue_2596_);
return v_defValue_2596_;
}
else
{
lean_object* v_val_2599_; 
v_val_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_val_2599_);
lean_dec_ref_known(v___x_2598_, 1);
if (lean_obj_tag(v_val_2599_) == 3)
{
lean_object* v_v_2600_; 
v_v_2600_ = lean_ctor_get(v_val_2599_, 0);
lean_inc(v_v_2600_);
lean_dec_ref_known(v_val_2599_, 1);
return v_v_2600_;
}
else
{
lean_dec(v_val_2599_);
lean_inc(v_defValue_2596_);
return v_defValue_2596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2601_, lean_object* v_opt_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2601_, v_opt_2602_);
lean_dec_ref(v_opt_2602_);
lean_dec_ref(v_opts_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_e_2604_){
_start:
{
if (lean_obj_tag(v_e_2604_) == 0)
{
uint8_t v___x_2605_; 
v___x_2605_ = 2;
return v___x_2605_;
}
else
{
uint8_t v___x_2606_; 
v___x_2606_ = 0;
return v___x_2606_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_e_2607_){
_start:
{
uint8_t v_res_2608_; lean_object* v_r_2609_; 
v_res_2608_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_e_2607_);
lean_dec_ref(v_e_2607_);
v_r_2609_ = lean_box(v_res_2608_);
return v_r_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t v_sz_2610_, size_t v_i_2611_, lean_object* v_bs_2612_){
_start:
{
uint8_t v___x_2613_; 
v___x_2613_ = lean_usize_dec_lt(v_i_2611_, v_sz_2610_);
if (v___x_2613_ == 0)
{
return v_bs_2612_;
}
else
{
lean_object* v_v_2614_; lean_object* v_msg_2615_; lean_object* v___x_2616_; lean_object* v_bs_x27_2617_; size_t v___x_2618_; size_t v___x_2619_; lean_object* v___x_2620_; 
v_v_2614_ = lean_array_uget_borrowed(v_bs_2612_, v_i_2611_);
v_msg_2615_ = lean_ctor_get(v_v_2614_, 1);
lean_inc_ref(v_msg_2615_);
v___x_2616_ = lean_unsigned_to_nat(0u);
v_bs_x27_2617_ = lean_array_uset(v_bs_2612_, v_i_2611_, v___x_2616_);
v___x_2618_ = ((size_t)1ULL);
v___x_2619_ = lean_usize_add(v_i_2611_, v___x_2618_);
v___x_2620_ = lean_array_uset(v_bs_x27_2617_, v_i_2611_, v_msg_2615_);
v_i_2611_ = v___x_2619_;
v_bs_2612_ = v___x_2620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2622_, lean_object* v_i_2623_, lean_object* v_bs_2624_){
_start:
{
size_t v_sz_boxed_2625_; size_t v_i_boxed_2626_; lean_object* v_res_2627_; 
v_sz_boxed_2625_ = lean_unbox_usize(v_sz_2622_);
lean_dec(v_sz_2622_);
v_i_boxed_2626_ = lean_unbox_usize(v_i_2623_);
lean_dec(v_i_2623_);
v_res_2627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_boxed_2625_, v_i_boxed_2626_, v_bs_2624_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object* v_oldTraces_2628_, lean_object* v_data_2629_, lean_object* v_ref_2630_, lean_object* v_msg_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_fileName_2637_; lean_object* v_fileMap_2638_; lean_object* v_options_2639_; lean_object* v_currRecDepth_2640_; lean_object* v_maxRecDepth_2641_; lean_object* v_ref_2642_; lean_object* v_currNamespace_2643_; lean_object* v_openDecls_2644_; lean_object* v_initHeartbeats_2645_; lean_object* v_maxHeartbeats_2646_; lean_object* v_quotContext_2647_; lean_object* v_currMacroScope_2648_; uint8_t v_diag_2649_; lean_object* v_cancelTk_x3f_2650_; uint8_t v_suppressElabErrors_2651_; lean_object* v_inheritedTraceOptions_2652_; lean_object* v___x_2653_; lean_object* v_traceState_2654_; lean_object* v_traces_2655_; lean_object* v_ref_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; size_t v_sz_2659_; size_t v___x_2660_; lean_object* v___x_2661_; lean_object* v_msg_2662_; lean_object* v___x_2663_; lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2701_; 
v_fileName_2637_ = lean_ctor_get(v___y_2634_, 0);
v_fileMap_2638_ = lean_ctor_get(v___y_2634_, 1);
v_options_2639_ = lean_ctor_get(v___y_2634_, 2);
v_currRecDepth_2640_ = lean_ctor_get(v___y_2634_, 3);
v_maxRecDepth_2641_ = lean_ctor_get(v___y_2634_, 4);
v_ref_2642_ = lean_ctor_get(v___y_2634_, 5);
v_currNamespace_2643_ = lean_ctor_get(v___y_2634_, 6);
v_openDecls_2644_ = lean_ctor_get(v___y_2634_, 7);
v_initHeartbeats_2645_ = lean_ctor_get(v___y_2634_, 8);
v_maxHeartbeats_2646_ = lean_ctor_get(v___y_2634_, 9);
v_quotContext_2647_ = lean_ctor_get(v___y_2634_, 10);
v_currMacroScope_2648_ = lean_ctor_get(v___y_2634_, 11);
v_diag_2649_ = lean_ctor_get_uint8(v___y_2634_, sizeof(void*)*14);
v_cancelTk_x3f_2650_ = lean_ctor_get(v___y_2634_, 12);
v_suppressElabErrors_2651_ = lean_ctor_get_uint8(v___y_2634_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2652_ = lean_ctor_get(v___y_2634_, 13);
v___x_2653_ = lean_st_ref_get(v___y_2635_);
v_traceState_2654_ = lean_ctor_get(v___x_2653_, 4);
lean_inc_ref(v_traceState_2654_);
lean_dec(v___x_2653_);
v_traces_2655_ = lean_ctor_get(v_traceState_2654_, 0);
lean_inc_ref(v_traces_2655_);
lean_dec_ref(v_traceState_2654_);
v_ref_2656_ = l_Lean_replaceRef(v_ref_2630_, v_ref_2642_);
lean_inc_ref(v_inheritedTraceOptions_2652_);
lean_inc(v_cancelTk_x3f_2650_);
lean_inc(v_currMacroScope_2648_);
lean_inc(v_quotContext_2647_);
lean_inc(v_maxHeartbeats_2646_);
lean_inc(v_initHeartbeats_2645_);
lean_inc(v_openDecls_2644_);
lean_inc(v_currNamespace_2643_);
lean_inc(v_maxRecDepth_2641_);
lean_inc(v_currRecDepth_2640_);
lean_inc_ref(v_options_2639_);
lean_inc_ref(v_fileMap_2638_);
lean_inc_ref(v_fileName_2637_);
v___x_2657_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2657_, 0, v_fileName_2637_);
lean_ctor_set(v___x_2657_, 1, v_fileMap_2638_);
lean_ctor_set(v___x_2657_, 2, v_options_2639_);
lean_ctor_set(v___x_2657_, 3, v_currRecDepth_2640_);
lean_ctor_set(v___x_2657_, 4, v_maxRecDepth_2641_);
lean_ctor_set(v___x_2657_, 5, v_ref_2656_);
lean_ctor_set(v___x_2657_, 6, v_currNamespace_2643_);
lean_ctor_set(v___x_2657_, 7, v_openDecls_2644_);
lean_ctor_set(v___x_2657_, 8, v_initHeartbeats_2645_);
lean_ctor_set(v___x_2657_, 9, v_maxHeartbeats_2646_);
lean_ctor_set(v___x_2657_, 10, v_quotContext_2647_);
lean_ctor_set(v___x_2657_, 11, v_currMacroScope_2648_);
lean_ctor_set(v___x_2657_, 12, v_cancelTk_x3f_2650_);
lean_ctor_set(v___x_2657_, 13, v_inheritedTraceOptions_2652_);
lean_ctor_set_uint8(v___x_2657_, sizeof(void*)*14, v_diag_2649_);
lean_ctor_set_uint8(v___x_2657_, sizeof(void*)*14 + 1, v_suppressElabErrors_2651_);
v___x_2658_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2655_);
lean_dec_ref(v_traces_2655_);
v_sz_2659_ = lean_array_size(v___x_2658_);
v___x_2660_ = ((size_t)0ULL);
v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_2659_, v___x_2660_, v___x_2658_);
v_msg_2662_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2662_, 0, v_data_2629_);
lean_ctor_set(v_msg_2662_, 1, v_msg_2631_);
lean_ctor_set(v_msg_2662_, 2, v___x_2661_);
v___x_2663_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2662_, v___y_2632_, v___y_2633_, v___x_2657_, v___y_2635_);
lean_dec_ref_known(v___x_2657_, 14);
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2666_ = v___x_2663_;
v_isShared_2667_ = v_isSharedCheck_2701_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2663_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2701_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v_traceState_2669_; lean_object* v_env_2670_; lean_object* v_nextMacroScope_2671_; lean_object* v_ngen_2672_; lean_object* v_auxDeclNGen_2673_; lean_object* v_cache_2674_; lean_object* v_messages_2675_; lean_object* v_infoState_2676_; lean_object* v_snapshotTasks_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2700_; 
v___x_2668_ = lean_st_ref_take(v___y_2635_);
v_traceState_2669_ = lean_ctor_get(v___x_2668_, 4);
v_env_2670_ = lean_ctor_get(v___x_2668_, 0);
v_nextMacroScope_2671_ = lean_ctor_get(v___x_2668_, 1);
v_ngen_2672_ = lean_ctor_get(v___x_2668_, 2);
v_auxDeclNGen_2673_ = lean_ctor_get(v___x_2668_, 3);
v_cache_2674_ = lean_ctor_get(v___x_2668_, 5);
v_messages_2675_ = lean_ctor_get(v___x_2668_, 6);
v_infoState_2676_ = lean_ctor_get(v___x_2668_, 7);
v_snapshotTasks_2677_ = lean_ctor_get(v___x_2668_, 8);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2679_ = v___x_2668_;
v_isShared_2680_ = v_isSharedCheck_2700_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_snapshotTasks_2677_);
lean_inc(v_infoState_2676_);
lean_inc(v_messages_2675_);
lean_inc(v_cache_2674_);
lean_inc(v_traceState_2669_);
lean_inc(v_auxDeclNGen_2673_);
lean_inc(v_ngen_2672_);
lean_inc(v_nextMacroScope_2671_);
lean_inc(v_env_2670_);
lean_dec(v___x_2668_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2700_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
uint64_t v_tid_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2698_; 
v_tid_2681_ = lean_ctor_get_uint64(v_traceState_2669_, sizeof(void*)*1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_traceState_2669_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v_traceState_2669_, 0);
lean_dec(v_unused_2699_);
v___x_2683_ = v_traceState_2669_;
v_isShared_2684_ = v_isSharedCheck_2698_;
goto v_resetjp_2682_;
}
else
{
lean_dec(v_traceState_2669_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2698_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v_ref_2630_);
lean_ctor_set(v___x_2685_, 1, v_a_2664_);
v___x_2686_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2628_, v___x_2685_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2686_);
v___x_2688_ = v___x_2683_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2686_);
lean_ctor_set_uint64(v_reuseFailAlloc_2697_, sizeof(void*)*1, v_tid_2681_);
v___x_2688_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2690_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 4, v___x_2688_);
v___x_2690_ = v___x_2679_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_env_2670_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_nextMacroScope_2671_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_ngen_2672_);
lean_ctor_set(v_reuseFailAlloc_2696_, 3, v_auxDeclNGen_2673_);
lean_ctor_set(v_reuseFailAlloc_2696_, 4, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2696_, 5, v_cache_2674_);
lean_ctor_set(v_reuseFailAlloc_2696_, 6, v_messages_2675_);
lean_ctor_set(v_reuseFailAlloc_2696_, 7, v_infoState_2676_);
lean_ctor_set(v_reuseFailAlloc_2696_, 8, v_snapshotTasks_2677_);
v___x_2690_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2691_ = lean_st_ref_set(v___y_2635_, v___x_2690_);
v___x_2692_ = lean_box(0);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2692_);
v___x_2694_ = v___x_2666_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_2702_, lean_object* v_data_2703_, lean_object* v_ref_2704_, lean_object* v_msg_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2702_, v_data_2703_, v_ref_2704_, v_msg_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
return v_res_2711_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_2714_ = l_Lean_stringToMessageData(v___x_2713_);
return v___x_2714_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2715_; double v___x_2716_; 
v___x_2715_ = lean_unsigned_to_nat(1000u);
v___x_2716_ = lean_float_of_nat(v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_2717_, uint8_t v_collapsed_2718_, lean_object* v_tag_2719_, lean_object* v_opts_2720_, uint8_t v_clsEnabled_2721_, lean_object* v_oldTraces_2722_, lean_object* v_msg_2723_, lean_object* v_resStartStop_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_fst_2733_; lean_object* v_snd_2734_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v_data_2738_; lean_object* v_fst_2749_; lean_object* v_snd_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; lean_object* v___y_2754_; lean_object* v_a_2755_; uint8_t v___y_2770_; double v___y_2801_; 
v_fst_2733_ = lean_ctor_get(v_resStartStop_2724_, 0);
lean_inc(v_fst_2733_);
v_snd_2734_ = lean_ctor_get(v_resStartStop_2724_, 1);
lean_inc(v_snd_2734_);
lean_dec_ref(v_resStartStop_2724_);
v_fst_2749_ = lean_ctor_get(v_snd_2734_, 0);
lean_inc(v_fst_2749_);
v_snd_2750_ = lean_ctor_get(v_snd_2734_, 1);
lean_inc(v_snd_2750_);
lean_dec(v_snd_2734_);
v___x_2751_ = l_Lean_trace_profiler;
v___x_2752_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2720_, v___x_2751_);
if (v___x_2752_ == 0)
{
v___y_2770_ = v___x_2752_;
goto v___jp_2769_;
}
else
{
lean_object* v___x_2806_; uint8_t v___x_2807_; 
v___x_2806_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2807_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2720_, v___x_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2809_; double v___x_2810_; double v___x_2811_; double v___x_2812_; 
v___x_2808_ = l_Lean_trace_profiler_threshold;
v___x_2809_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2720_, v___x_2808_);
v___x_2810_ = lean_float_of_nat(v___x_2809_);
v___x_2811_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_2812_ = lean_float_div(v___x_2810_, v___x_2811_);
v___y_2801_ = v___x_2812_;
goto v___jp_2800_;
}
else
{
lean_object* v___x_2813_; lean_object* v___x_2814_; double v___x_2815_; 
v___x_2813_ = l_Lean_trace_profiler_threshold;
v___x_2814_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2720_, v___x_2813_);
v___x_2815_ = lean_float_of_nat(v___x_2814_);
v___y_2801_ = v___x_2815_;
goto v___jp_2800_;
}
}
v___jp_2735_:
{
lean_object* v___x_2739_; 
lean_inc(v___y_2736_);
v___x_2739_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2722_, v_data_2738_, v___y_2736_, v___y_2737_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v___x_2740_; 
lean_dec_ref_known(v___x_2739_, 1);
v___x_2740_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2733_);
return v___x_2740_;
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_fst_2733_);
v_a_2741_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2739_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2739_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
v___jp_2753_:
{
uint8_t v_result_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; double v___x_2759_; lean_object* v_data_2760_; 
v_result_2756_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_fst_2733_);
v___x_2757_ = lean_box(v_result_2756_);
v___x_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
v___x_2759_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
lean_inc_ref(v_tag_2719_);
lean_inc_ref(v___x_2758_);
lean_inc(v_cls_2717_);
v_data_2760_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2760_, 0, v_cls_2717_);
lean_ctor_set(v_data_2760_, 1, v___x_2758_);
lean_ctor_set(v_data_2760_, 2, v_tag_2719_);
lean_ctor_set_float(v_data_2760_, sizeof(void*)*3, v___x_2759_);
lean_ctor_set_float(v_data_2760_, sizeof(void*)*3 + 8, v___x_2759_);
lean_ctor_set_uint8(v_data_2760_, sizeof(void*)*3 + 16, v_collapsed_2718_);
if (v___x_2752_ == 0)
{
lean_dec_ref_known(v___x_2758_, 1);
lean_dec(v_snd_2750_);
lean_dec(v_fst_2749_);
lean_dec_ref(v_tag_2719_);
lean_dec(v_cls_2717_);
v___y_2736_ = v___y_2754_;
v___y_2737_ = v_a_2755_;
v_data_2738_ = v_data_2760_;
goto v___jp_2735_;
}
else
{
lean_object* v_data_2761_; double v___x_2762_; double v___x_2763_; 
lean_dec_ref_known(v_data_2760_, 3);
v_data_2761_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2761_, 0, v_cls_2717_);
lean_ctor_set(v_data_2761_, 1, v___x_2758_);
lean_ctor_set(v_data_2761_, 2, v_tag_2719_);
v___x_2762_ = lean_unbox_float(v_fst_2749_);
lean_dec(v_fst_2749_);
lean_ctor_set_float(v_data_2761_, sizeof(void*)*3, v___x_2762_);
v___x_2763_ = lean_unbox_float(v_snd_2750_);
lean_dec(v_snd_2750_);
lean_ctor_set_float(v_data_2761_, sizeof(void*)*3 + 8, v___x_2763_);
lean_ctor_set_uint8(v_data_2761_, sizeof(void*)*3 + 16, v_collapsed_2718_);
v___y_2736_ = v___y_2754_;
v___y_2737_ = v_a_2755_;
v_data_2738_ = v_data_2761_;
goto v___jp_2735_;
}
}
v___jp_2764_:
{
lean_object* v_ref_2765_; lean_object* v___x_2766_; 
v_ref_2765_ = lean_ctor_get(v___y_2730_, 5);
lean_inc(v___y_2731_);
lean_inc_ref(v___y_2730_);
lean_inc(v___y_2729_);
lean_inc_ref(v___y_2728_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v___y_2725_);
lean_inc(v_fst_2733_);
v___x_2766_ = lean_apply_9(v_msg_2723_, v_fst_2733_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, lean_box(0));
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
v___y_2754_ = v_ref_2765_;
v_a_2755_ = v_a_2767_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2768_; 
lean_dec_ref_known(v___x_2766_, 1);
v___x_2768_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_2754_ = v_ref_2765_;
v_a_2755_ = v___x_2768_;
goto v___jp_2753_;
}
}
v___jp_2769_:
{
if (v_clsEnabled_2721_ == 0)
{
if (v___y_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v_traceState_2772_; lean_object* v_env_2773_; lean_object* v_nextMacroScope_2774_; lean_object* v_ngen_2775_; lean_object* v_auxDeclNGen_2776_; lean_object* v_cache_2777_; lean_object* v_messages_2778_; lean_object* v_infoState_2779_; lean_object* v_snapshotTasks_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2799_; 
lean_dec(v_snd_2750_);
lean_dec(v_fst_2749_);
lean_dec_ref(v_msg_2723_);
lean_dec_ref(v_tag_2719_);
lean_dec(v_cls_2717_);
v___x_2771_ = lean_st_ref_take(v___y_2731_);
v_traceState_2772_ = lean_ctor_get(v___x_2771_, 4);
v_env_2773_ = lean_ctor_get(v___x_2771_, 0);
v_nextMacroScope_2774_ = lean_ctor_get(v___x_2771_, 1);
v_ngen_2775_ = lean_ctor_get(v___x_2771_, 2);
v_auxDeclNGen_2776_ = lean_ctor_get(v___x_2771_, 3);
v_cache_2777_ = lean_ctor_get(v___x_2771_, 5);
v_messages_2778_ = lean_ctor_get(v___x_2771_, 6);
v_infoState_2779_ = lean_ctor_get(v___x_2771_, 7);
v_snapshotTasks_2780_ = lean_ctor_get(v___x_2771_, 8);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2782_ = v___x_2771_;
v_isShared_2783_ = v_isSharedCheck_2799_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_snapshotTasks_2780_);
lean_inc(v_infoState_2779_);
lean_inc(v_messages_2778_);
lean_inc(v_cache_2777_);
lean_inc(v_traceState_2772_);
lean_inc(v_auxDeclNGen_2776_);
lean_inc(v_ngen_2775_);
lean_inc(v_nextMacroScope_2774_);
lean_inc(v_env_2773_);
lean_dec(v___x_2771_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2799_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
uint64_t v_tid_2784_; lean_object* v_traces_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2798_; 
v_tid_2784_ = lean_ctor_get_uint64(v_traceState_2772_, sizeof(void*)*1);
v_traces_2785_ = lean_ctor_get(v_traceState_2772_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_traceState_2772_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2787_ = v_traceState_2772_;
v_isShared_2788_ = v_isSharedCheck_2798_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_traces_2785_);
lean_dec(v_traceState_2772_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2798_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2791_; 
v___x_2789_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2722_, v_traces_2785_);
lean_dec_ref(v_traces_2785_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2789_);
v___x_2791_ = v___x_2787_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2789_);
lean_ctor_set_uint64(v_reuseFailAlloc_2797_, sizeof(void*)*1, v_tid_2784_);
v___x_2791_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2793_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 4, v___x_2791_);
v___x_2793_ = v___x_2782_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_env_2773_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_nextMacroScope_2774_);
lean_ctor_set(v_reuseFailAlloc_2796_, 2, v_ngen_2775_);
lean_ctor_set(v_reuseFailAlloc_2796_, 3, v_auxDeclNGen_2776_);
lean_ctor_set(v_reuseFailAlloc_2796_, 4, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2796_, 5, v_cache_2777_);
lean_ctor_set(v_reuseFailAlloc_2796_, 6, v_messages_2778_);
lean_ctor_set(v_reuseFailAlloc_2796_, 7, v_infoState_2779_);
lean_ctor_set(v_reuseFailAlloc_2796_, 8, v_snapshotTasks_2780_);
v___x_2793_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_st_ref_set(v___y_2731_, v___x_2793_);
v___x_2795_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2733_);
return v___x_2795_;
}
}
}
}
}
else
{
goto v___jp_2764_;
}
}
else
{
goto v___jp_2764_;
}
}
v___jp_2800_:
{
double v___x_2802_; double v___x_2803_; double v___x_2804_; uint8_t v___x_2805_; 
v___x_2802_ = lean_unbox_float(v_snd_2750_);
v___x_2803_ = lean_unbox_float(v_fst_2749_);
v___x_2804_ = lean_float_sub(v___x_2802_, v___x_2803_);
v___x_2805_ = lean_float_decLt(v___y_2801_, v___x_2804_);
v___y_2770_ = v___x_2805_;
goto v___jp_2769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object* v_cls_2816_, lean_object* v_collapsed_2817_, lean_object* v_tag_2818_, lean_object* v_opts_2819_, lean_object* v_clsEnabled_2820_, lean_object* v_oldTraces_2821_, lean_object* v_msg_2822_, lean_object* v_resStartStop_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
uint8_t v_collapsed_boxed_2832_; uint8_t v_clsEnabled_boxed_2833_; lean_object* v_res_2834_; 
v_collapsed_boxed_2832_ = lean_unbox(v_collapsed_2817_);
v_clsEnabled_boxed_2833_ = lean_unbox(v_clsEnabled_2820_);
v_res_2834_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2816_, v_collapsed_boxed_2832_, v_tag_2818_, v_opts_2819_, v_clsEnabled_boxed_2833_, v_oldTraces_2821_, v_msg_2822_, v_resStartStop_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v_opts_2819_);
return v_res_2834_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2(void){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1));
v___x_2839_ = l_Lean_stringToMessageData(v___x_2838_);
return v___x_2839_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4(void){
_start:
{
lean_object* v___x_2841_; double v___x_2842_; 
v___x_2841_ = lean_unsigned_to_nat(1000000000u);
v___x_2842_ = lean_float_of_nat(v___x_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object* v_P_2843_, lean_object* v_lhs_2844_, lean_object* v_rhs_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v_options_2874_; lean_object* v_inheritedTraceOptions_2875_; uint8_t v_hasTrace_2876_; lean_object* v_cls_2877_; lean_object* v___f_2878_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; uint8_t v_____do__lift_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; 
v_options_2874_ = lean_ctor_get(v_a_2851_, 2);
v_inheritedTraceOptions_2875_ = lean_ctor_get(v_a_2851_, 13);
v_hasTrace_2876_ = lean_ctor_get_uint8(v_options_2874_, sizeof(void*)*1);
v_cls_2877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_2878_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
if (v_hasTrace_2876_ == 0)
{
lean_object* v___x_2997_; lean_object* v_a_2998_; uint8_t v___x_2999_; 
v___x_2997_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2877_, v_inheritedTraceOptions_2875_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref(v___x_2997_);
v___x_2999_ = lean_unbox(v_a_2998_);
lean_dec(v_a_2998_);
v_____do__lift_2976_ = v___x_2999_;
v___y_2977_ = v_a_2846_;
v___y_2978_ = v_a_2847_;
v___y_2979_ = v_a_2848_;
v___y_2980_ = v_a_2849_;
v___y_2981_ = v_a_2850_;
v___y_2982_ = v_a_2851_;
v___y_2983_ = v_a_2852_;
goto v___jp_2975_;
}
else
{
lean_object* v___f_3000_; uint8_t v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v_a_3008_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v_a_3020_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v_a_3038_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v_a_3053_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; 
v___f_3000_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3));
v___x_3001_ = 0;
v___x_3002_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_3003_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3004_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2875_, v_options_2874_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3101_ = l_Lean_trace_profiler;
v___x_3102_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_2874_, v___x_3101_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3103_; lean_object* v_a_3104_; uint8_t v___x_3105_; 
v___x_3103_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2877_, v_inheritedTraceOptions_2875_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref(v___x_3103_);
v___x_3105_ = lean_unbox(v_a_3104_);
lean_dec(v_a_3104_);
v_____do__lift_2976_ = v___x_3105_;
v___y_2977_ = v_a_2846_;
v___y_2978_ = v_a_2847_;
v___y_2979_ = v_a_2848_;
v___y_2980_ = v_a_2849_;
v___y_2981_ = v_a_2850_;
v___y_2982_ = v_a_2851_;
v___y_2983_ = v_a_2852_;
goto v___jp_2975_;
}
else
{
goto v___jp_3068_;
}
}
else
{
goto v___jp_3068_;
}
v___jp_3005_:
{
lean_object* v___x_3009_; double v___x_3010_; double v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3009_ = lean_io_get_num_heartbeats();
v___x_3010_ = lean_float_of_nat(v___y_3007_);
v___x_3011_ = lean_float_of_nat(v___x_3009_);
v___x_3012_ = lean_box_float(v___x_3010_);
v___x_3013_ = lean_box_float(v___x_3011_);
v___x_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3012_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v___x_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3015_, 0, v_a_3008_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2877_, v___x_3001_, v___x_3002_, v_options_2874_, v___x_3004_, v___y_3006_, v___f_3000_, v___x_3015_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
return v___x_3016_;
}
v___jp_3017_:
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_a_3020_);
v___y_3006_ = v___y_3018_;
v___y_3007_ = v___y_3019_;
v_a_3008_ = v___x_3021_;
goto v___jp_3005_;
}
v___jp_3022_:
{
if (lean_obj_tag(v___y_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
v_a_3026_ = lean_ctor_get(v___y_3025_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___y_3025_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___y_3025_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___y_3025_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set_tag(v___x_3028_, 1);
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
v___y_3006_ = v___y_3023_;
v___y_3007_ = v___y_3024_;
v_a_3008_ = v___x_3031_;
goto v___jp_3005_;
}
}
}
else
{
lean_object* v_a_3034_; 
v_a_3034_ = lean_ctor_get(v___y_3025_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___y_3025_, 1);
v___y_3018_ = v___y_3023_;
v___y_3019_ = v___y_3024_;
v_a_3020_ = v_a_3034_;
goto v___jp_3017_;
}
}
v___jp_3035_:
{
lean_object* v___x_3039_; double v___x_3040_; double v___x_3041_; double v___x_3042_; double v___x_3043_; double v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3039_ = lean_io_mono_nanos_now();
v___x_3040_ = lean_float_of_nat(v___y_3037_);
v___x_3041_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4);
v___x_3042_ = lean_float_div(v___x_3040_, v___x_3041_);
v___x_3043_ = lean_float_of_nat(v___x_3039_);
v___x_3044_ = lean_float_div(v___x_3043_, v___x_3041_);
v___x_3045_ = lean_box_float(v___x_3042_);
v___x_3046_ = lean_box_float(v___x_3044_);
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3045_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3048_, 0, v_a_3038_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2877_, v___x_3001_, v___x_3002_, v_options_2874_, v___x_3004_, v___y_3036_, v___f_3000_, v___x_3048_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
return v___x_3049_;
}
v___jp_3050_:
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v_a_3053_);
v___y_3036_ = v___y_3051_;
v___y_3037_ = v___y_3052_;
v_a_3038_ = v___x_3054_;
goto v___jp_3035_;
}
v___jp_3055_:
{
if (lean_obj_tag(v___y_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
v_a_3059_ = lean_ctor_get(v___y_3058_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___y_3058_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___y_3058_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___y_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
lean_ctor_set_tag(v___x_3061_, 1);
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
v___y_3036_ = v___y_3056_;
v___y_3037_ = v___y_3057_;
v_a_3038_ = v___x_3064_;
goto v___jp_3035_;
}
}
}
else
{
lean_object* v_a_3067_; 
v_a_3067_ = lean_ctor_get(v___y_3058_, 0);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___y_3058_, 1);
v___y_3051_ = v___y_3056_;
v___y_3052_ = v___y_3057_;
v_a_3053_ = v_a_3067_;
goto v___jp_3050_;
}
}
v___jp_3068_:
{
lean_object* v___x_3069_; lean_object* v_a_3070_; lean_object* v___x_3071_; uint8_t v___x_3072_; 
v___x_3069_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_2852_);
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_a_3070_);
lean_dec_ref(v___x_3069_);
v___x_3071_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3072_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_2874_, v___x_3071_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v_a_3075_; uint8_t v___x_3076_; 
v___x_3073_ = lean_io_mono_nanos_now();
v___x_3074_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2877_, v_inheritedTraceOptions_2875_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3075_);
lean_dec_ref(v___x_3074_);
v___x_3076_ = lean_unbox(v_a_3075_);
lean_dec(v_a_3075_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = lean_box(0);
v___x_3078_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2844_, v_rhs_2845_, v___f_2878_, v_cls_2877_, v___x_3072_, v_P_2843_, v_hasTrace_2876_, v___x_3077_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
v___y_3056_ = v_a_3070_;
v___y_3057_ = v___x_3073_;
v___y_3058_ = v___x_3078_;
goto v___jp_3055_;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3079_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2845_);
lean_inc_ref(v_lhs_2844_);
lean_inc_ref(v_P_2843_);
v___x_3080_ = l_Lean_mkAppB(v_P_2843_, v_lhs_2844_, v_rhs_2845_);
v___x_3081_ = l_Lean_indentExpr(v___x_3080_);
v___x_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3079_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2877_, v___x_3082_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3085_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
v___x_3085_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2844_, v_rhs_2845_, v___f_2878_, v_cls_2877_, v___x_3072_, v_P_2843_, v_hasTrace_2876_, v_a_3084_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
v___y_3056_ = v_a_3070_;
v___y_3057_ = v___x_3073_;
v___y_3058_ = v___x_3085_;
goto v___jp_3055_;
}
else
{
lean_object* v_a_3086_; 
lean_dec_ref(v_rhs_2845_);
lean_dec_ref(v_lhs_2844_);
lean_dec_ref(v_P_2843_);
v_a_3086_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3083_, 1);
v___y_3051_ = v_a_3070_;
v___y_3052_ = v___x_3073_;
v_a_3053_ = v_a_3086_;
goto v___jp_3050_;
}
}
}
else
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v_a_3089_; uint8_t v___x_3090_; 
v___x_3087_ = lean_io_get_num_heartbeats();
v___x_3088_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2877_, v_inheritedTraceOptions_2875_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref(v___x_3088_);
v___x_3090_ = lean_unbox(v_a_3089_);
lean_dec(v_a_3089_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = lean_box(0);
v___x_3092_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__8(v_lhs_2844_, v_rhs_2845_, v_P_2843_, v___x_3072_, v_cls_2877_, v___f_2878_, v___x_3091_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
v___y_3023_ = v_a_3070_;
v___y_3024_ = v___x_3087_;
v___y_3025_ = v___x_3092_;
goto v___jp_3022_;
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3093_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2845_);
lean_inc_ref(v_lhs_2844_);
lean_inc_ref(v_P_2843_);
v___x_3094_ = l_Lean_mkAppB(v_P_2843_, v_lhs_2844_, v_rhs_2845_);
v___x_3095_ = l_Lean_indentExpr(v___x_3094_);
v___x_3096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3093_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2877_, v___x_3096_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3099_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v___x_3099_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__8(v_lhs_2844_, v_rhs_2845_, v_P_2843_, v___x_3072_, v_cls_2877_, v___f_2878_, v_a_3098_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
v___y_3023_ = v_a_3070_;
v___y_3024_ = v___x_3087_;
v___y_3025_ = v___x_3099_;
goto v___jp_3022_;
}
else
{
lean_object* v_a_3100_; 
lean_dec_ref(v_rhs_2845_);
lean_dec_ref(v_lhs_2844_);
lean_dec_ref(v_P_2843_);
v_a_3100_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3100_);
lean_dec_ref_known(v___x_3097_, 1);
v___y_3018_ = v_a_3070_;
v___y_3019_ = v___x_3087_;
v_a_3020_ = v_a_3100_;
goto v___jp_3017_;
}
}
}
}
}
v___jp_2854_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
return v___x_2856_;
}
v___jp_2857_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
return v___x_2859_;
}
v___jp_2860_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
return v___x_2862_;
}
v___jp_2863_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2870_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8);
v___x_2871_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2872_, 0, v___y_2865_);
lean_ctor_set(v___x_2872_, 1, v___x_2870_);
lean_ctor_set(v___x_2872_, 2, v___x_2871_);
v___x_2873_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2864_, v___x_2872_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
return v___x_2873_;
}
v___jp_2879_:
{
lean_object* v___x_2887_; 
lean_inc_ref(v_lhs_2844_);
v___x_2887_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2844_);
if (lean_obj_tag(v___x_2887_) == 1)
{
lean_object* v_val_2888_; lean_object* v___x_2889_; 
v_val_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_val_2888_);
lean_dec_ref_known(v___x_2887_, 1);
lean_inc_ref(v_rhs_2845_);
v___x_2889_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2845_);
if (lean_obj_tag(v___x_2889_) == 1)
{
lean_object* v_val_2890_; uint8_t v___x_2891_; 
v_val_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_val_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v___x_2891_ = lean_expr_eqv(v_val_2888_, v_val_2890_);
if (v___x_2891_ == 0)
{
lean_object* v_inheritedTraceOptions_2892_; lean_object* v___x_2893_; lean_object* v_a_2894_; uint8_t v___x_2895_; 
lean_dec_ref(v_P_2843_);
v_inheritedTraceOptions_2892_ = lean_ctor_get(v___y_2885_, 13);
v___x_2893_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2877_, v_inheritedTraceOptions_2892_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref(v___x_2893_);
v___x_2895_ = lean_unbox(v_a_2894_);
lean_dec(v_a_2894_);
if (v___x_2895_ == 0)
{
lean_dec(v_val_2890_);
lean_dec(v_val_2888_);
lean_dec_ref(v_rhs_2845_);
lean_dec_ref(v_lhs_2844_);
goto v___jp_2860_;
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2896_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2);
v___x_2897_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2888_);
v___x_2898_ = l_Lean_MessageData_ofExpr(v___x_2897_);
v___x_2899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2896_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = l_Lean_indentExpr(v_lhs_2844_);
v___x_2903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2890_);
v___x_2907_ = l_Lean_MessageData_ofExpr(v___x_2906_);
v___x_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2905_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v___x_2900_);
v___x_2910_ = l_Lean_indentExpr(v_rhs_2845_);
v___x_2911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2877_, v___x_2911_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_dec_ref_known(v___x_2912_, 1);
goto v___jp_2860_;
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2912_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2912_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
}
else
{
lean_object* v_options_2921_; lean_object* v_inheritedTraceOptions_2922_; uint8_t v_hasTrace_2923_; lean_object* v___x_2924_; lean_object* v___f_2925_; 
lean_dec(v_val_2890_);
v_options_2921_ = lean_ctor_get(v___y_2885_, 2);
v_inheritedTraceOptions_2922_ = lean_ctor_get(v___y_2885_, 13);
v_hasTrace_2923_ = lean_ctor_get_uint8(v_options_2921_, sizeof(void*)*1);
v___x_2924_ = lean_box(v___x_2891_);
lean_inc(v_val_2888_);
v___f_2925_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 11, 5);
lean_closure_set(v___f_2925_, 0, v_val_2888_);
lean_closure_set(v___f_2925_, 1, v_lhs_2844_);
lean_closure_set(v___f_2925_, 2, v_rhs_2845_);
lean_closure_set(v___f_2925_, 3, v_P_2843_);
lean_closure_set(v___f_2925_, 4, v___x_2924_);
if (v_hasTrace_2923_ == 0)
{
v___y_2864_ = v___f_2925_;
v___y_2865_ = v_val_2888_;
v___y_2866_ = v___y_2883_;
v___y_2867_ = v___y_2884_;
v___y_2868_ = v___y_2885_;
v___y_2869_ = v___y_2886_;
goto v___jp_2863_;
}
else
{
lean_object* v___x_2926_; uint8_t v___x_2927_; 
v___x_2926_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_2927_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2922_, v_options_2921_, v___x_2926_);
if (v___x_2927_ == 0)
{
v___y_2864_ = v___f_2925_;
v___y_2865_ = v_val_2888_;
v___y_2866_ = v___y_2883_;
v___y_2867_ = v___y_2884_;
v___y_2868_ = v___y_2885_;
v___y_2869_ = v___y_2886_;
goto v___jp_2863_;
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2928_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11);
lean_inc(v_val_2888_);
v___x_2929_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2888_);
v___x_2930_ = l_Lean_MessageData_ofExpr(v___x_2929_);
v___x_2931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2928_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
v___x_2932_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13);
v___x_2933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2931_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
v___x_2934_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2877_, v___x_2933_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_dec_ref_known(v___x_2934_, 1);
v___y_2864_ = v___f_2925_;
v___y_2865_ = v_val_2888_;
v___y_2866_ = v___y_2883_;
v___y_2867_ = v___y_2884_;
v___y_2868_ = v___y_2885_;
v___y_2869_ = v___y_2886_;
goto v___jp_2863_;
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec_ref(v___f_2925_);
lean_dec(v_val_2888_);
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2934_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2943_; lean_object* v___x_2944_; lean_object* v_a_2945_; uint8_t v___x_2946_; 
lean_dec(v___x_2889_);
lean_dec(v_val_2888_);
lean_dec_ref(v_lhs_2844_);
lean_dec_ref(v_P_2843_);
v_inheritedTraceOptions_2943_ = lean_ctor_get(v___y_2885_, 13);
v___x_2944_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2877_, v_inheritedTraceOptions_2943_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2944_);
v___x_2946_ = lean_unbox(v_a_2945_);
lean_dec(v_a_2945_);
if (v___x_2946_ == 0)
{
lean_dec_ref(v_rhs_2845_);
goto v___jp_2857_;
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2947_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2948_ = l_Lean_indentExpr(v_rhs_2845_);
v___x_2949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2947_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
v___x_2950_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2877_, v___x_2949_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_dec_ref_known(v___x_2950_, 1);
goto v___jp_2857_;
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2950_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2959_; lean_object* v___x_2960_; lean_object* v_a_2961_; uint8_t v___x_2962_; 
lean_dec(v___x_2887_);
lean_dec_ref(v_rhs_2845_);
lean_dec_ref(v_P_2843_);
v_inheritedTraceOptions_2959_ = lean_ctor_get(v___y_2885_, 13);
v___x_2960_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2877_, v_inheritedTraceOptions_2959_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref(v___x_2960_);
v___x_2962_ = lean_unbox(v_a_2961_);
lean_dec(v_a_2961_);
if (v___x_2962_ == 0)
{
lean_dec_ref(v_lhs_2844_);
goto v___jp_2854_;
}
else
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2963_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__15);
v___x_2964_ = l_Lean_indentExpr(v_lhs_2844_);
v___x_2965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2877_, v___x_2965_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_dec_ref_known(v___x_2966_, 1);
goto v___jp_2854_;
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2966_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2966_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
}
v___jp_2975_:
{
if (v_____do__lift_2976_ == 0)
{
v___y_2880_ = v___y_2977_;
v___y_2881_ = v___y_2978_;
v___y_2882_ = v___y_2979_;
v___y_2883_ = v___y_2980_;
v___y_2884_ = v___y_2981_;
v___y_2885_ = v___y_2982_;
v___y_2886_ = v___y_2983_;
goto v___jp_2879_;
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2984_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2845_);
lean_inc_ref(v_lhs_2844_);
lean_inc_ref(v_P_2843_);
v___x_2985_ = l_Lean_mkAppB(v_P_2843_, v_lhs_2844_, v_rhs_2845_);
v___x_2986_ = l_Lean_indentExpr(v___x_2985_);
v___x_2987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2984_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2877_, v___x_2987_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_dec_ref_known(v___x_2988_, 1);
v___y_2880_ = v___y_2977_;
v___y_2881_ = v___y_2978_;
v___y_2882_ = v___y_2979_;
v___y_2883_ = v___y_2980_;
v___y_2884_ = v___y_2981_;
v___y_2885_ = v___y_2982_;
v___y_2886_ = v___y_2983_;
goto v___jp_2879_;
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v_rhs_2845_);
lean_dec_ref(v_lhs_2844_);
lean_dec_ref(v_P_2843_);
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2988_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2988_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3106_, lean_object* v_lhs_3107_, lean_object* v_rhs_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v_P_3106_, v_lhs_3107_, v_rhs_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_);
lean_dec(v_a_3115_);
lean_dec_ref(v_a_3114_);
lean_dec(v_a_3113_);
lean_dec_ref(v_a_3112_);
lean_dec(v_a_3111_);
lean_dec_ref(v_a_3110_);
lean_dec(v_a_3109_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3118_, lean_object* v_msg_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3118_, v_msg_3119_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3129_, lean_object* v_msg_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(v_cls_3129_, v_msg_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_00_u03b1_3140_, lean_object* v_x_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_3141_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3151_, lean_object* v_x_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_00_u03b1_3151_, v_x_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_oldTraces_3162_, lean_object* v_data_3163_, lean_object* v_ref_3164_, lean_object* v_msg_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3162_, v_data_3163_, v_ref_3164_, v_msg_3165_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_oldTraces_3175_, lean_object* v_data_3176_, lean_object* v_ref_3177_, lean_object* v_msg_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_oldTraces_3175_, v_data_3176_, v_ref_3177_, v_msg_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
return v_res_3187_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5));
v___x_3198_ = l_Lean_stringToMessageData(v___x_3197_);
return v___x_3198_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7(void){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = l_Lean_checkEmoji;
v___x_3200_ = l_Lean_stringToMessageData(v___x_3199_);
return v___x_3200_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3201_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7);
v___x_3202_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6);
v___x_3203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
lean_ctor_set(v___x_3203_, 1, v___x_3201_);
return v___x_3203_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10(void){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3205_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9));
v___x_3206_ = l_Lean_stringToMessageData(v___x_3205_);
return v___x_3206_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11(void){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10);
v___x_3208_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v___x_3207_);
return v___x_3209_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__13(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__12));
v___x_3212_ = l_Lean_stringToMessageData(v___x_3211_);
return v___x_3212_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__14(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__13);
v___x_3214_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
lean_ctor_set(v___x_3215_, 1, v___x_3213_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object* v_e_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3216_, v_a_3221_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3332_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3332_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3332_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3235_ = l_Lean_Expr_cleanupAnnotations(v_a_3226_);
v___x_3236_ = l_Lean_Expr_isApp(v___x_3235_);
if (v___x_3236_ == 0)
{
lean_dec_ref(v___x_3235_);
goto v___jp_3230_;
}
else
{
lean_object* v_arg_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v_arg_3237_ = lean_ctor_get(v___x_3235_, 1);
lean_inc_ref(v_arg_3237_);
v___x_3238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3235_);
v___x_3239_ = l_Lean_Expr_isApp(v___x_3238_);
if (v___x_3239_ == 0)
{
lean_dec_ref(v___x_3238_);
lean_dec_ref(v_arg_3237_);
goto v___jp_3230_;
}
else
{
lean_object* v_arg_3240_; lean_object* v___x_3241_; uint8_t v___x_3242_; 
v_arg_3240_ = lean_ctor_get(v___x_3238_, 1);
lean_inc_ref(v_arg_3240_);
v___x_3241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3238_);
v___x_3242_ = l_Lean_Expr_isApp(v___x_3241_);
if (v___x_3242_ == 0)
{
lean_dec_ref(v___x_3241_);
lean_dec_ref(v_arg_3240_);
lean_dec_ref(v_arg_3237_);
goto v___jp_3230_;
}
else
{
lean_object* v_arg_3243_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___x_3268_; lean_object* v___x_3269_; uint8_t v___x_3270_; 
v_arg_3243_ = lean_ctor_get(v___x_3241_, 1);
lean_inc_ref(v_arg_3243_);
v___x_3268_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3241_);
v___x_3269_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1));
v___x_3270_ = l_Lean_Expr_isConstOf(v___x_3268_, v___x_3269_);
if (v___x_3270_ == 0)
{
uint8_t v___x_3271_; 
v___x_3271_ = l_Lean_Expr_isApp(v___x_3268_);
if (v___x_3271_ == 0)
{
lean_dec_ref(v___x_3268_);
lean_dec_ref(v_arg_3243_);
lean_dec_ref(v_arg_3240_);
lean_dec_ref(v_arg_3237_);
goto v___jp_3230_;
}
else
{
lean_object* v_arg_3272_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___x_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; 
v_arg_3272_ = lean_ctor_get(v___x_3268_, 1);
lean_inc_ref(v_arg_3272_);
v___x_3297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3268_);
v___x_3298_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4));
v___x_3299_ = l_Lean_Expr_isConstOf(v___x_3297_, v___x_3298_);
lean_dec_ref(v___x_3297_);
if (v___x_3299_ == 0)
{
lean_dec_ref(v_arg_3272_);
lean_dec_ref(v_arg_3243_);
lean_dec_ref(v_arg_3240_);
lean_dec_ref(v_arg_3237_);
goto v___jp_3230_;
}
else
{
lean_object* v_options_3300_; uint8_t v_hasTrace_3301_; 
lean_del_object(v___x_3228_);
v_options_3300_ = lean_ctor_get(v_a_3222_, 2);
v_hasTrace_3301_ = lean_ctor_get_uint8(v_options_3300_, sizeof(void*)*1);
if (v_hasTrace_3301_ == 0)
{
v___y_3274_ = v_a_3217_;
v___y_3275_ = v_a_3218_;
v___y_3276_ = v_a_3219_;
v___y_3277_ = v_a_3220_;
v___y_3278_ = v_a_3221_;
v___y_3279_ = v_a_3222_;
v___y_3280_ = v_a_3223_;
goto v___jp_3273_;
}
else
{
lean_object* v_inheritedTraceOptions_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v_inheritedTraceOptions_3302_ = lean_ctor_get(v_a_3222_, 13);
v___x_3303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3305_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3302_, v_options_3300_, v___x_3304_);
if (v___x_3305_ == 0)
{
v___y_3274_ = v_a_3217_;
v___y_3275_ = v_a_3218_;
v___y_3276_ = v_a_3219_;
v___y_3277_ = v_a_3220_;
v___y_3278_ = v_a_3221_;
v___y_3279_ = v_a_3222_;
v___y_3280_ = v_a_3223_;
goto v___jp_3273_;
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11);
v___x_3307_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3303_, v___x_3306_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_dec_ref_known(v___x_3307_, 1);
v___y_3274_ = v_a_3217_;
v___y_3275_ = v_a_3218_;
v___y_3276_ = v_a_3219_;
v___y_3277_ = v_a_3220_;
v___y_3278_ = v_a_3221_;
v___y_3279_ = v_a_3222_;
v___y_3280_ = v_a_3223_;
goto v___jp_3273_;
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_dec_ref(v_arg_3272_);
lean_dec_ref(v_arg_3243_);
lean_dec_ref(v_arg_3240_);
lean_dec_ref(v_arg_3237_);
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
}
v___jp_3273_:
{
lean_object* v___x_3281_; 
lean_inc_ref(v_arg_3272_);
v___x_3281_ = l_Lean_Meta_getDecLevel(v_arg_3272_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3281_, 1);
v___x_3283_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4));
v___x_3284_ = lean_box(0);
v___x_3285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3285_, 0, v_a_3282_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = l_Lean_Expr_const___override(v___x_3283_, v___x_3285_);
v___x_3287_ = l_Lean_mkAppB(v___x_3286_, v_arg_3272_, v_arg_3243_);
v___x_3288_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3287_, v_arg_3240_, v_arg_3237_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
return v___x_3288_;
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec_ref(v_arg_3272_);
lean_dec_ref(v_arg_3243_);
lean_dec_ref(v_arg_3240_);
lean_dec_ref(v_arg_3237_);
v_a_3289_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3281_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3281_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
}
else
{
lean_object* v_options_3316_; uint8_t v_hasTrace_3317_; 
lean_dec_ref(v___x_3268_);
lean_del_object(v___x_3228_);
v_options_3316_ = lean_ctor_get(v_a_3222_, 2);
v_hasTrace_3317_ = lean_ctor_get_uint8(v_options_3316_, sizeof(void*)*1);
if (v_hasTrace_3317_ == 0)
{
v___y_3245_ = v_a_3217_;
v___y_3246_ = v_a_3218_;
v___y_3247_ = v_a_3219_;
v___y_3248_ = v_a_3220_;
v___y_3249_ = v_a_3221_;
v___y_3250_ = v_a_3222_;
v___y_3251_ = v_a_3223_;
goto v___jp_3244_;
}
else
{
lean_object* v_inheritedTraceOptions_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
v_inheritedTraceOptions_3318_ = lean_ctor_get(v_a_3222_, 13);
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3320_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3321_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3318_, v_options_3316_, v___x_3320_);
if (v___x_3321_ == 0)
{
v___y_3245_ = v_a_3217_;
v___y_3246_ = v_a_3218_;
v___y_3247_ = v_a_3219_;
v___y_3248_ = v_a_3220_;
v___y_3249_ = v_a_3221_;
v___y_3250_ = v_a_3222_;
v___y_3251_ = v_a_3223_;
goto v___jp_3244_;
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__14);
v___x_3323_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3319_, v___x_3322_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_dec_ref_known(v___x_3323_, 1);
v___y_3245_ = v_a_3217_;
v___y_3246_ = v_a_3218_;
v___y_3247_ = v_a_3219_;
v___y_3248_ = v_a_3220_;
v___y_3249_ = v_a_3221_;
v___y_3250_ = v_a_3222_;
v___y_3251_ = v_a_3223_;
goto v___jp_3244_;
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_dec_ref(v_arg_3243_);
lean_dec_ref(v_arg_3240_);
lean_dec_ref(v_arg_3237_);
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3323_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3323_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
}
}
v___jp_3244_:
{
lean_object* v___x_3252_; 
lean_inc_ref(v_arg_3243_);
v___x_3252_ = l_Lean_Meta_getLevel(v_arg_3243_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref_known(v___x_3252_, 1);
v___x_3254_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1));
v___x_3255_ = lean_box(0);
v___x_3256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3256_, 0, v_a_3253_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = l_Lean_Expr_const___override(v___x_3254_, v___x_3256_);
v___x_3258_ = l_Lean_Expr_app___override(v___x_3257_, v_arg_3243_);
v___x_3259_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3258_, v_arg_3240_, v_arg_3237_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
return v___x_3259_;
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec_ref(v_arg_3243_);
lean_dec_ref(v_arg_3240_);
lean_dec_ref(v_arg_3237_);
v_a_3260_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3252_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3252_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
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
}
}
v___jp_3230_:
{
lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3231_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3231_);
v___x_3233_ = v___x_3228_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
v_a_3333_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3225_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3225_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object* v_e_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(v_e_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec(v_a_3346_);
lean_dec_ref(v_a_3345_);
lean_dec(v_a_3344_);
lean_dec_ref(v_a_3343_);
lean_dec(v_a_3342_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__0(lean_object* v_x_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__0___boxed(lean_object* v_x_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__0(v_x_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v_x_3362_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1(lean_object* v_x_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1___closed__0));
v___x_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3383_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1___boxed(lean_object* v_x_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1(v_x_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v_x_3385_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__2(lean_object* v_e_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3404_, 0, v_e_3395_);
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__2___boxed(lean_object* v_e_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__2(v_e_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__3(lean_object* v_x_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = lean_box(0);
v___x_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__3___boxed(lean_object* v_x_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__3(v_x_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v_x_3427_);
return v_res_3436_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__5(void){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3443_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6(void){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__5);
v___x_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
return v___x_3445_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__7(void){
_start:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = lean_unsigned_to_nat(0u);
v___x_3447_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6);
v___x_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
lean_ctor_set(v___x_3448_, 1, v___x_3446_);
return v___x_3448_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__8(void){
_start:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3449_ = lean_unsigned_to_nat(32u);
v___x_3450_ = lean_mk_empty_array_with_capacity(v___x_3449_);
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__9(void){
_start:
{
size_t v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3452_ = ((size_t)5ULL);
v___x_3453_ = lean_unsigned_to_nat(0u);
v___x_3454_ = lean_unsigned_to_nat(32u);
v___x_3455_ = lean_mk_empty_array_with_capacity(v___x_3454_);
v___x_3456_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__8);
v___x_3457_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
lean_ctor_set(v___x_3457_, 1, v___x_3455_);
lean_ctor_set(v___x_3457_, 2, v___x_3453_);
lean_ctor_set(v___x_3457_, 3, v___x_3453_);
lean_ctor_set_usize(v___x_3457_, 4, v___x_3452_);
return v___x_3457_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__10(void){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3458_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__9);
v___x_3459_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6);
v___x_3460_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
lean_ctor_set(v___x_3460_, 2, v___x_3459_);
lean_ctor_set(v___x_3460_, 3, v___x_3458_);
return v___x_3460_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11(void){
_start:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3461_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__10);
v___x_3462_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__7);
v___x_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
lean_ctor_set(v___x_3463_, 1, v___x_3461_);
return v___x_3463_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__12(void){
_start:
{
uint8_t v___x_3464_; lean_object* v___f_3465_; lean_object* v___f_3466_; lean_object* v___f_3467_; lean_object* v___x_3468_; lean_object* v___f_3469_; lean_object* v___x_3470_; 
v___x_3464_ = 1;
v___f_3465_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__4));
v___f_3466_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__3));
v___f_3467_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__2));
v___x_3468_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 9, 0);
v___f_3469_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__1));
v___x_3470_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3470_, 0, v___f_3469_);
lean_ctor_set(v___x_3470_, 1, v___x_3468_);
lean_ctor_set(v___x_3470_, 2, v___f_3467_);
lean_ctor_set(v___x_3470_, 3, v___f_3466_);
lean_ctor_set(v___x_3470_, 4, v___f_3465_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*5, v___x_3464_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget(lean_object* v_mvarId_3471_, lean_object* v_maxSteps_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_3476_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v___x_3480_; lean_object* v_maxDischargeDepth_3481_; uint8_t v_contextual_3482_; uint8_t v_memoize_3483_; uint8_t v_singlePass_3484_; uint8_t v_zeta_3485_; uint8_t v_beta_3486_; uint8_t v_eta_3487_; uint8_t v_etaStruct_3488_; uint8_t v_iota_3489_; uint8_t v_proj_3490_; uint8_t v_decide_3491_; uint8_t v_arith_3492_; uint8_t v_autoUnfold_3493_; uint8_t v_dsimp_3494_; uint8_t v_failIfUnchanged_3495_; uint8_t v_ground_3496_; uint8_t v_unfoldPartialApp_3497_; uint8_t v_zetaDelta_3498_; uint8_t v_index_3499_; uint8_t v_implicitDefEqProofs_3500_; uint8_t v_zetaUnused_3501_; uint8_t v_catchRuntime_3502_; uint8_t v_zetaHave_3503_; uint8_t v_letToHave_3504_; uint8_t v_congrConsts_3505_; uint8_t v_bitVecOfNat_3506_; uint8_t v_warnExponents_3507_; uint8_t v_suggestions_3508_; lean_object* v_maxSuggestions_3509_; uint8_t v_locals_3510_; uint8_t v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
v___x_3480_ = l_Lean_Meta_Simp_neutralConfig;
v_maxDischargeDepth_3481_ = lean_ctor_get(v___x_3480_, 1);
v_contextual_3482_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3);
v_memoize_3483_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 1);
v_singlePass_3484_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 2);
v_zeta_3485_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 3);
v_beta_3486_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 4);
v_eta_3487_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 5);
v_etaStruct_3488_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 6);
v_iota_3489_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 7);
v_proj_3490_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 8);
v_decide_3491_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 9);
v_arith_3492_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 10);
v_autoUnfold_3493_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 11);
v_dsimp_3494_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 12);
v_failIfUnchanged_3495_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 13);
v_ground_3496_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_3497_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 15);
v_zetaDelta_3498_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 16);
v_index_3499_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_3500_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 18);
v_zetaUnused_3501_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 19);
v_catchRuntime_3502_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 20);
v_zetaHave_3503_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 21);
v_letToHave_3504_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 22);
v_congrConsts_3505_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 23);
v_bitVecOfNat_3506_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 24);
v_warnExponents_3507_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 25);
v_suggestions_3508_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 26);
v_maxSuggestions_3509_ = lean_ctor_get(v___x_3480_, 2);
v_locals_3510_ = lean_ctor_get_uint8(v___x_3480_, sizeof(void*)*3 + 27);
v___x_3511_ = 1;
lean_inc(v_maxSuggestions_3509_);
lean_inc(v_maxDischargeDepth_3481_);
v___x_3512_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3512_, 0, v_maxSteps_3472_);
lean_ctor_set(v___x_3512_, 1, v_maxDischargeDepth_3481_);
lean_ctor_set(v___x_3512_, 2, v_maxSuggestions_3509_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3, v_contextual_3482_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 1, v_memoize_3483_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 2, v_singlePass_3484_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 3, v_zeta_3485_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 4, v_beta_3486_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 5, v_eta_3487_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 6, v_etaStruct_3488_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 7, v_iota_3489_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 8, v_proj_3490_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 9, v_decide_3491_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 10, v_arith_3492_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 11, v_autoUnfold_3493_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 12, v_dsimp_3494_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 13, v_failIfUnchanged_3495_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 14, v_ground_3496_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 15, v_unfoldPartialApp_3497_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 16, v_zetaDelta_3498_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 17, v_index_3499_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_3500_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 19, v_zetaUnused_3501_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 20, v_catchRuntime_3502_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 21, v_zetaHave_3503_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 22, v_letToHave_3504_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 23, v_congrConsts_3505_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 24, v_bitVecOfNat_3506_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 25, v_warnExponents_3507_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 26, v_suggestions_3508_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 27, v_locals_3510_);
lean_ctor_set_uint8(v___x_3512_, sizeof(void*)*3 + 28, v___x_3511_);
v___x_3513_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__0));
v___x_3514_ = l_Lean_Options_empty;
v___x_3515_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3512_, v___x_3513_, v_a_3479_, v___x_3514_, v_a_3473_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
lean_inc(v_mvarId_3471_);
v___x_3517_ = l_Lean_MVarId_getType(v_mvarId_3471_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3519_; lean_object* v_a_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___x_3517_, 1);
v___x_3519_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_3518_, v_a_3474_);
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc_n(v_a_3520_, 2);
lean_dec_ref(v___x_3519_);
v___x_3521_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11);
v___x_3522_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__12);
v___x_3523_ = l_Lean_Meta_Simp_main(v_a_3520_, v_a_3516_, v___x_3521_, v___x_3522_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v_fst_3525_; lean_object* v___x_3526_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v_fst_3525_ = lean_ctor_get(v_a_3524_, 0);
lean_inc(v_fst_3525_);
lean_dec(v_a_3524_);
v___x_3526_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_3471_, v_a_3520_, v_fst_3525_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
lean_dec(v_a_3520_);
return v___x_3526_;
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec(v_a_3520_);
lean_dec(v_mvarId_3471_);
v_a_3527_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3523_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3523_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec(v_a_3516_);
lean_dec(v_mvarId_3471_);
v_a_3535_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3517_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3517_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec(v_mvarId_3471_);
v_a_3543_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3515_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3515_);
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
lean_dec(v_maxSteps_3472_);
lean_dec(v_mvarId_3471_);
v_a_3551_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3478_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3478_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___boxed(lean_object* v_mvarId_3559_, lean_object* v_maxSteps_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget(v_mvarId_3559_, v_maxSteps_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___redArg(lean_object* v_mvarId_3567_, lean_object* v_x_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3567_, v_x_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3574_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
v_a_3583_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3574_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3574_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___redArg___boxed(lean_object* v_mvarId_3591_, lean_object* v_x_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___redArg(v_mvarId_3591_, v_x_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0(lean_object* v_00_u03b1_3599_, lean_object* v_mvarId_3600_, lean_object* v_x_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___redArg(v_mvarId_3600_, v_x_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___boxed(lean_object* v_00_u03b1_3608_, lean_object* v_mvarId_3609_, lean_object* v_x_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0(v_00_u03b1_3608_, v_mvarId_3609_, v_x_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___lam__4(lean_object* v_maxSteps_3617_, lean_object* v_fvarId_3618_, lean_object* v___f_3619_, lean_object* v___f_3620_, lean_object* v___f_3621_, lean_object* v___f_3622_, lean_object* v_goal_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_3627_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v___x_3631_; lean_object* v_maxDischargeDepth_3632_; uint8_t v_contextual_3633_; uint8_t v_memoize_3634_; uint8_t v_singlePass_3635_; uint8_t v_zeta_3636_; uint8_t v_beta_3637_; uint8_t v_eta_3638_; uint8_t v_etaStruct_3639_; uint8_t v_iota_3640_; uint8_t v_proj_3641_; uint8_t v_decide_3642_; uint8_t v_arith_3643_; uint8_t v_autoUnfold_3644_; uint8_t v_dsimp_3645_; uint8_t v_failIfUnchanged_3646_; uint8_t v_ground_3647_; uint8_t v_unfoldPartialApp_3648_; uint8_t v_zetaDelta_3649_; uint8_t v_index_3650_; uint8_t v_implicitDefEqProofs_3651_; uint8_t v_zetaUnused_3652_; uint8_t v_catchRuntime_3653_; uint8_t v_zetaHave_3654_; uint8_t v_letToHave_3655_; uint8_t v_congrConsts_3656_; uint8_t v_bitVecOfNat_3657_; uint8_t v_warnExponents_3658_; uint8_t v_suggestions_3659_; lean_object* v_maxSuggestions_3660_; uint8_t v_locals_3661_; uint8_t v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref_known(v___x_3629_, 1);
v___x_3631_ = l_Lean_Meta_Simp_neutralConfig;
v_maxDischargeDepth_3632_ = lean_ctor_get(v___x_3631_, 1);
v_contextual_3633_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3);
v_memoize_3634_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 1);
v_singlePass_3635_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 2);
v_zeta_3636_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 3);
v_beta_3637_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 4);
v_eta_3638_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 5);
v_etaStruct_3639_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 6);
v_iota_3640_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 7);
v_proj_3641_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 8);
v_decide_3642_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 9);
v_arith_3643_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 10);
v_autoUnfold_3644_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 11);
v_dsimp_3645_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 12);
v_failIfUnchanged_3646_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 13);
v_ground_3647_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_3648_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 15);
v_zetaDelta_3649_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 16);
v_index_3650_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_3651_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 18);
v_zetaUnused_3652_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 19);
v_catchRuntime_3653_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 20);
v_zetaHave_3654_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 21);
v_letToHave_3655_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 22);
v_congrConsts_3656_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 23);
v_bitVecOfNat_3657_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 24);
v_warnExponents_3658_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 25);
v_suggestions_3659_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 26);
v_maxSuggestions_3660_ = lean_ctor_get(v___x_3631_, 2);
v_locals_3661_ = lean_ctor_get_uint8(v___x_3631_, sizeof(void*)*3 + 27);
v___x_3662_ = 1;
lean_inc(v_maxSuggestions_3660_);
lean_inc(v_maxDischargeDepth_3632_);
v___x_3663_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3663_, 0, v_maxSteps_3617_);
lean_ctor_set(v___x_3663_, 1, v_maxDischargeDepth_3632_);
lean_ctor_set(v___x_3663_, 2, v_maxSuggestions_3660_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3, v_contextual_3633_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 1, v_memoize_3634_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 2, v_singlePass_3635_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 3, v_zeta_3636_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 4, v_beta_3637_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 5, v_eta_3638_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 6, v_etaStruct_3639_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 7, v_iota_3640_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 8, v_proj_3641_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 9, v_decide_3642_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 10, v_arith_3643_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 11, v_autoUnfold_3644_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 12, v_dsimp_3645_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 13, v_failIfUnchanged_3646_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 14, v_ground_3647_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 15, v_unfoldPartialApp_3648_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 16, v_zetaDelta_3649_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 17, v_index_3650_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_3651_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 19, v_zetaUnused_3652_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 20, v_catchRuntime_3653_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 21, v_zetaHave_3654_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 22, v_letToHave_3655_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 23, v_congrConsts_3656_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 24, v_bitVecOfNat_3657_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 25, v_warnExponents_3658_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 26, v_suggestions_3659_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 27, v_locals_3661_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*3 + 28, v___x_3662_);
v___x_3664_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__0));
v___x_3665_ = l_Lean_Options_empty;
v___x_3666_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3663_, v___x_3664_, v_a_3630_, v___x_3665_, v___y_3624_, v___y_3626_, v___y_3627_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
lean_inc(v_fvarId_3618_);
v___x_3668_ = l_Lean_FVarId_getType___redArg(v_fvarId_3618_, v___y_3624_, v___y_3626_, v___y_3627_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3670_; lean_object* v_a_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
lean_dec_ref_known(v___x_3668_, 1);
v___x_3670_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_3669_, v___y_3625_);
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref(v___x_3670_);
v___x_3672_ = lean_unsigned_to_nat(32u);
v___x_3673_ = lean_mk_empty_array_with_capacity(v___x_3672_);
lean_dec_ref(v___x_3673_);
v___x_3674_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11);
v___x_3675_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 9, 0);
v___x_3676_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3676_, 0, v___f_3619_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
lean_ctor_set(v___x_3676_, 2, v___f_3620_);
lean_ctor_set(v___x_3676_, 3, v___f_3621_);
lean_ctor_set(v___x_3676_, 4, v___f_3622_);
lean_ctor_set_uint8(v___x_3676_, sizeof(void*)*5, v___x_3662_);
v___x_3677_ = l_Lean_Meta_Simp_main(v_a_3671_, v_a_3667_, v___x_3674_, v___x_3676_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v_fst_3679_; uint8_t v___x_3680_; lean_object* v___x_3681_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref_known(v___x_3677_, 1);
v_fst_3679_ = lean_ctor_get(v_a_3678_, 0);
lean_inc(v_fst_3679_);
lean_dec(v_a_3678_);
v___x_3680_ = 0;
v___x_3681_ = l_Lean_Meta_applySimpResultToLocalDecl(v_goal_3623_, v_fvarId_3618_, v_fst_3679_, v___x_3680_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3702_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3684_ = v___x_3681_;
v_isShared_3685_ = v_isSharedCheck_3702_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3681_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3702_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
if (lean_obj_tag(v_a_3682_) == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3688_; 
v___x_3686_ = lean_box(0);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3686_);
v___x_3688_ = v___x_3684_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
else
{
lean_object* v_val_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3701_; 
v_val_3690_ = lean_ctor_get(v_a_3682_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v_a_3682_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3692_ = v_a_3682_;
v_isShared_3693_ = v_isSharedCheck_3701_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_val_3690_);
lean_dec(v_a_3682_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3701_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v_snd_3694_; lean_object* v___x_3696_; 
v_snd_3694_ = lean_ctor_get(v_val_3690_, 1);
lean_inc(v_snd_3694_);
lean_dec(v_val_3690_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 0, v_snd_3694_);
v___x_3696_ = v___x_3692_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_snd_3694_);
v___x_3696_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3698_; 
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3696_);
v___x_3698_ = v___x_3684_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
v_a_3703_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3681_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3681_);
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
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v_goal_3623_);
lean_dec(v_fvarId_3618_);
v_a_3711_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3677_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3677_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_dec(v_a_3667_);
lean_dec(v_goal_3623_);
lean_dec_ref(v___f_3622_);
lean_dec_ref(v___f_3621_);
lean_dec_ref(v___f_3620_);
lean_dec_ref(v___f_3619_);
lean_dec(v_fvarId_3618_);
v_a_3719_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3668_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3668_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec(v_goal_3623_);
lean_dec_ref(v___f_3622_);
lean_dec_ref(v___f_3621_);
lean_dec_ref(v___f_3620_);
lean_dec_ref(v___f_3619_);
lean_dec(v_fvarId_3618_);
v_a_3727_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3666_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3666_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_dec(v_goal_3623_);
lean_dec_ref(v___f_3622_);
lean_dec_ref(v___f_3621_);
lean_dec_ref(v___f_3620_);
lean_dec_ref(v___f_3619_);
lean_dec(v_fvarId_3618_);
lean_dec(v_maxSteps_3617_);
v_a_3735_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3629_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3629_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___lam__4___boxed(lean_object* v_maxSteps_3743_, lean_object* v_fvarId_3744_, lean_object* v___f_3745_, lean_object* v___f_3746_, lean_object* v___f_3747_, lean_object* v___f_3748_, lean_object* v_goal_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___lam__4(v_maxSteps_3743_, v_fvarId_3744_, v___f_3745_, v___f_3746_, v___f_3747_, v___f_3748_, v_goal_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta(lean_object* v_goal_3756_, lean_object* v_fvarId_3757_, lean_object* v_maxSteps_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_){
_start:
{
lean_object* v___f_3764_; lean_object* v___f_3765_; lean_object* v___f_3766_; lean_object* v___f_3767_; lean_object* v___f_3768_; lean_object* v___x_3769_; 
v___f_3764_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__4));
v___f_3765_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__3));
v___f_3766_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__2));
v___f_3767_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__1));
lean_inc(v_goal_3756_);
v___f_3768_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___lam__4___boxed), 12, 7);
lean_closure_set(v___f_3768_, 0, v_maxSteps_3758_);
lean_closure_set(v___f_3768_, 1, v_fvarId_3757_);
lean_closure_set(v___f_3768_, 2, v___f_3767_);
lean_closure_set(v___f_3768_, 3, v___f_3766_);
lean_closure_set(v___f_3768_, 4, v___f_3765_);
lean_closure_set(v___f_3768_, 5, v___f_3764_);
lean_closure_set(v___f_3768_, 6, v_goal_3756_);
v___x_3769_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___redArg(v_goal_3756_, v___f_3768_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___boxed(lean_object* v_goal_3770_, lean_object* v_fvarId_3771_, lean_object* v_maxSteps_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta(v_goal_3770_, v_fvarId_3771_, v_maxSteps_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(lean_object* v_x_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v___x_3787_; 
lean_inc(v___y_3781_);
lean_inc_ref(v___y_3780_);
v___x_3787_ = lean_apply_7(v_x_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, lean_box(0));
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed(lean_object* v_x_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(v_x_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg(lean_object* v_mvarId_3797_, lean_object* v_x_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___f_3806_; lean_object* v___x_3807_; 
lean_inc(v___y_3800_);
lean_inc_ref(v___y_3799_);
v___f_3806_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3806_, 0, v_x_3798_);
lean_closure_set(v___f_3806_, 1, v___y_3799_);
lean_closure_set(v___f_3806_, 2, v___y_3800_);
v___x_3807_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3797_, v___f_3806_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
if (lean_obj_tag(v___x_3807_) == 0)
{
return v___x_3807_;
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3807_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3807_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___boxed(lean_object* v_mvarId_3816_, lean_object* v_x_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg(v_mvarId_3816_, v_x_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4(lean_object* v_00_u03b1_3826_, lean_object* v_mvarId_3827_, lean_object* v_x_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v___x_3836_; 
v___x_3836_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg(v_mvarId_3827_, v_x_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___boxed(lean_object* v_00_u03b1_3837_, lean_object* v_mvarId_3838_, lean_object* v_x_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4(v_00_u03b1_3837_, v_mvarId_3838_, v_x_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
return v_res_3847_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(lean_object* v_a_3848_, lean_object* v_x_3849_){
_start:
{
if (lean_obj_tag(v_x_3849_) == 0)
{
uint8_t v___x_3850_; 
v___x_3850_ = 0;
return v___x_3850_;
}
else
{
lean_object* v_key_3851_; lean_object* v_tail_3852_; uint8_t v___x_3853_; 
v_key_3851_ = lean_ctor_get(v_x_3849_, 0);
v_tail_3852_ = lean_ctor_get(v_x_3849_, 2);
v___x_3853_ = l_Lean_instBEqFVarId_beq(v_key_3851_, v_a_3848_);
if (v___x_3853_ == 0)
{
v_x_3849_ = v_tail_3852_;
goto _start;
}
else
{
return v___x_3853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg___boxed(lean_object* v_a_3855_, lean_object* v_x_3856_){
_start:
{
uint8_t v_res_3857_; lean_object* v_r_3858_; 
v_res_3857_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3855_, v_x_3856_);
lean_dec(v_x_3856_);
lean_dec(v_a_3855_);
v_r_3858_ = lean_box(v_res_3857_);
return v_r_3858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_x_3859_, lean_object* v_x_3860_){
_start:
{
if (lean_obj_tag(v_x_3860_) == 0)
{
return v_x_3859_;
}
else
{
lean_object* v_key_3861_; lean_object* v_value_3862_; lean_object* v_tail_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3886_; 
v_key_3861_ = lean_ctor_get(v_x_3860_, 0);
v_value_3862_ = lean_ctor_get(v_x_3860_, 1);
v_tail_3863_ = lean_ctor_get(v_x_3860_, 2);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_x_3860_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3865_ = v_x_3860_;
v_isShared_3866_ = v_isSharedCheck_3886_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_tail_3863_);
lean_inc(v_value_3862_);
lean_inc(v_key_3861_);
lean_dec(v_x_3860_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3886_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3867_; uint64_t v___x_3868_; uint64_t v___x_3869_; uint64_t v___x_3870_; uint64_t v_fold_3871_; uint64_t v___x_3872_; uint64_t v___x_3873_; uint64_t v___x_3874_; size_t v___x_3875_; size_t v___x_3876_; size_t v___x_3877_; size_t v___x_3878_; size_t v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3882_; 
v___x_3867_ = lean_array_get_size(v_x_3859_);
v___x_3868_ = l_Lean_instHashableFVarId_hash(v_key_3861_);
v___x_3869_ = 32ULL;
v___x_3870_ = lean_uint64_shift_right(v___x_3868_, v___x_3869_);
v_fold_3871_ = lean_uint64_xor(v___x_3868_, v___x_3870_);
v___x_3872_ = 16ULL;
v___x_3873_ = lean_uint64_shift_right(v_fold_3871_, v___x_3872_);
v___x_3874_ = lean_uint64_xor(v_fold_3871_, v___x_3873_);
v___x_3875_ = lean_uint64_to_usize(v___x_3874_);
v___x_3876_ = lean_usize_of_nat(v___x_3867_);
v___x_3877_ = ((size_t)1ULL);
v___x_3878_ = lean_usize_sub(v___x_3876_, v___x_3877_);
v___x_3879_ = lean_usize_land(v___x_3875_, v___x_3878_);
v___x_3880_ = lean_array_uget_borrowed(v_x_3859_, v___x_3879_);
lean_inc(v___x_3880_);
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 2, v___x_3880_);
v___x_3882_ = v___x_3865_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_key_3861_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v_value_3862_);
lean_ctor_set(v_reuseFailAlloc_3885_, 2, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3883_; 
v___x_3883_ = lean_array_uset(v_x_3859_, v___x_3879_, v___x_3882_);
v_x_3859_ = v___x_3883_;
v_x_3860_ = v_tail_3863_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(lean_object* v_i_3887_, lean_object* v_source_3888_, lean_object* v_target_3889_){
_start:
{
lean_object* v___x_3890_; uint8_t v___x_3891_; 
v___x_3890_ = lean_array_get_size(v_source_3888_);
v___x_3891_ = lean_nat_dec_lt(v_i_3887_, v___x_3890_);
if (v___x_3891_ == 0)
{
lean_dec_ref(v_source_3888_);
lean_dec(v_i_3887_);
return v_target_3889_;
}
else
{
lean_object* v_es_3892_; lean_object* v___x_3893_; lean_object* v_source_3894_; lean_object* v_target_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v_es_3892_ = lean_array_fget(v_source_3888_, v_i_3887_);
v___x_3893_ = lean_box(0);
v_source_3894_ = lean_array_fset(v_source_3888_, v_i_3887_, v___x_3893_);
v_target_3895_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(v_target_3889_, v_es_3892_);
v___x_3896_ = lean_unsigned_to_nat(1u);
v___x_3897_ = lean_nat_add(v_i_3887_, v___x_3896_);
lean_dec(v_i_3887_);
v_i_3887_ = v___x_3897_;
v_source_3888_ = v_source_3894_;
v_target_3889_ = v_target_3895_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(lean_object* v_data_3899_){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v_nbuckets_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3900_ = lean_array_get_size(v_data_3899_);
v___x_3901_ = lean_unsigned_to_nat(2u);
v_nbuckets_3902_ = lean_nat_mul(v___x_3900_, v___x_3901_);
v___x_3903_ = lean_unsigned_to_nat(0u);
v___x_3904_ = lean_box(0);
v___x_3905_ = lean_mk_array(v_nbuckets_3902_, v___x_3904_);
v___x_3906_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(v___x_3903_, v_data_3899_, v___x_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_m_3907_, lean_object* v_a_3908_, lean_object* v_b_3909_){
_start:
{
lean_object* v_size_3910_; lean_object* v_buckets_3911_; lean_object* v___x_3912_; uint64_t v___x_3913_; uint64_t v___x_3914_; uint64_t v___x_3915_; uint64_t v_fold_3916_; uint64_t v___x_3917_; uint64_t v___x_3918_; uint64_t v___x_3919_; size_t v___x_3920_; size_t v___x_3921_; size_t v___x_3922_; size_t v___x_3923_; size_t v___x_3924_; lean_object* v_bkt_3925_; uint8_t v___x_3926_; 
v_size_3910_ = lean_ctor_get(v_m_3907_, 0);
v_buckets_3911_ = lean_ctor_get(v_m_3907_, 1);
v___x_3912_ = lean_array_get_size(v_buckets_3911_);
v___x_3913_ = l_Lean_instHashableFVarId_hash(v_a_3908_);
v___x_3914_ = 32ULL;
v___x_3915_ = lean_uint64_shift_right(v___x_3913_, v___x_3914_);
v_fold_3916_ = lean_uint64_xor(v___x_3913_, v___x_3915_);
v___x_3917_ = 16ULL;
v___x_3918_ = lean_uint64_shift_right(v_fold_3916_, v___x_3917_);
v___x_3919_ = lean_uint64_xor(v_fold_3916_, v___x_3918_);
v___x_3920_ = lean_uint64_to_usize(v___x_3919_);
v___x_3921_ = lean_usize_of_nat(v___x_3912_);
v___x_3922_ = ((size_t)1ULL);
v___x_3923_ = lean_usize_sub(v___x_3921_, v___x_3922_);
v___x_3924_ = lean_usize_land(v___x_3920_, v___x_3923_);
v_bkt_3925_ = lean_array_uget_borrowed(v_buckets_3911_, v___x_3924_);
v___x_3926_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3908_, v_bkt_3925_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3947_; 
lean_inc_ref(v_buckets_3911_);
lean_inc(v_size_3910_);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_m_3907_);
if (v_isSharedCheck_3947_ == 0)
{
lean_object* v_unused_3948_; lean_object* v_unused_3949_; 
v_unused_3948_ = lean_ctor_get(v_m_3907_, 1);
lean_dec(v_unused_3948_);
v_unused_3949_ = lean_ctor_get(v_m_3907_, 0);
lean_dec(v_unused_3949_);
v___x_3928_ = v_m_3907_;
v_isShared_3929_ = v_isSharedCheck_3947_;
goto v_resetjp_3927_;
}
else
{
lean_dec(v_m_3907_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3947_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3930_; lean_object* v_size_x27_3931_; lean_object* v___x_3932_; lean_object* v_buckets_x27_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
v___x_3930_ = lean_unsigned_to_nat(1u);
v_size_x27_3931_ = lean_nat_add(v_size_3910_, v___x_3930_);
lean_dec(v_size_3910_);
lean_inc(v_bkt_3925_);
v___x_3932_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3932_, 0, v_a_3908_);
lean_ctor_set(v___x_3932_, 1, v_b_3909_);
lean_ctor_set(v___x_3932_, 2, v_bkt_3925_);
v_buckets_x27_3933_ = lean_array_uset(v_buckets_3911_, v___x_3924_, v___x_3932_);
v___x_3934_ = lean_unsigned_to_nat(4u);
v___x_3935_ = lean_nat_mul(v_size_x27_3931_, v___x_3934_);
v___x_3936_ = lean_unsigned_to_nat(3u);
v___x_3937_ = lean_nat_div(v___x_3935_, v___x_3936_);
lean_dec(v___x_3935_);
v___x_3938_ = lean_array_get_size(v_buckets_x27_3933_);
v___x_3939_ = lean_nat_dec_le(v___x_3937_, v___x_3938_);
lean_dec(v___x_3937_);
if (v___x_3939_ == 0)
{
lean_object* v_val_3940_; lean_object* v___x_3942_; 
v_val_3940_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(v_buckets_x27_3933_);
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 1, v_val_3940_);
lean_ctor_set(v___x_3928_, 0, v_size_x27_3931_);
v___x_3942_ = v___x_3928_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_size_x27_3931_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_val_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
else
{
lean_object* v___x_3945_; 
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 1, v_buckets_x27_3933_);
lean_ctor_set(v___x_3928_, 0, v_size_x27_3931_);
v___x_3945_ = v___x_3928_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_size_x27_3931_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_buckets_x27_3933_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
else
{
lean_dec(v_b_3909_);
lean_dec(v_a_3908_);
return v_m_3907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(lean_object* v_as_3950_, size_t v_i_3951_, size_t v_stop_3952_, lean_object* v_b_3953_, lean_object* v___y_3954_){
_start:
{
uint8_t v___x_3956_; 
v___x_3956_ = lean_usize_dec_eq(v_i_3951_, v_stop_3952_);
if (v___x_3956_ == 0)
{
lean_object* v___x_3957_; lean_object* v_rewriteCache_3958_; lean_object* v_acNfCache_3959_; lean_object* v_typeAnalysis_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3974_; 
v___x_3957_ = lean_st_ref_take(v___y_3954_);
v_rewriteCache_3958_ = lean_ctor_get(v___x_3957_, 0);
v_acNfCache_3959_ = lean_ctor_get(v___x_3957_, 1);
v_typeAnalysis_3960_ = lean_ctor_get(v___x_3957_, 2);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3962_ = v___x_3957_;
v_isShared_3963_ = v_isSharedCheck_3974_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_typeAnalysis_3960_);
lean_inc(v_acNfCache_3959_);
lean_inc(v_rewriteCache_3958_);
lean_dec(v___x_3957_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3974_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3968_; 
v___x_3964_ = lean_array_uget_borrowed(v_as_3950_, v_i_3951_);
v___x_3965_ = lean_box(0);
lean_inc(v___x_3964_);
v___x_3966_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_acNfCache_3959_, v___x_3964_, v___x_3965_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 1, v___x_3966_);
v___x_3968_ = v___x_3962_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_rewriteCache_3958_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v___x_3966_);
lean_ctor_set(v_reuseFailAlloc_3973_, 2, v_typeAnalysis_3960_);
v___x_3968_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
lean_object* v___x_3969_; size_t v___x_3970_; size_t v___x_3971_; 
v___x_3969_ = lean_st_ref_set(v___y_3954_, v___x_3968_);
v___x_3970_ = ((size_t)1ULL);
v___x_3971_ = lean_usize_add(v_i_3951_, v___x_3970_);
v_i_3951_ = v___x_3971_;
v_b_3953_ = v___x_3965_;
goto _start;
}
}
}
else
{
lean_object* v___x_3975_; 
v___x_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3975_, 0, v_b_3953_);
return v___x_3975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg___boxed(lean_object* v_as_3976_, lean_object* v_i_3977_, lean_object* v_stop_3978_, lean_object* v_b_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
size_t v_i_boxed_3982_; size_t v_stop_boxed_3983_; lean_object* v_res_3984_; 
v_i_boxed_3982_ = lean_unbox_usize(v_i_3977_);
lean_dec(v_i_3977_);
v_stop_boxed_3983_ = lean_unbox_usize(v_stop_3978_);
lean_dec(v_stop_3978_);
v_res_3984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(v_as_3976_, v_i_boxed_3982_, v_stop_boxed_3983_, v_b_3979_, v___y_3980_);
lean_dec(v___y_3980_);
lean_dec_ref(v_as_3976_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object* v___x_3985_, size_t v___x_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v___x_3994_; 
v___x_3994_ = l_Lean_Meta_getPropHyps(v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4013_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_3997_ = v___x_3994_;
v_isShared_3998_ = v_isSharedCheck_4013_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3994_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4013_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; 
v___x_3999_ = lean_array_get_size(v_a_3995_);
v___x_4000_ = lean_box(0);
v___x_4001_ = lean_nat_dec_lt(v___x_3985_, v___x_3999_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4003_; 
lean_dec(v_a_3995_);
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 0, v___x_4000_);
v___x_4003_ = v___x_3997_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_4000_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
else
{
uint8_t v___x_4005_; 
v___x_4005_ = lean_nat_dec_le(v___x_3999_, v___x_3999_);
if (v___x_4005_ == 0)
{
if (v___x_4001_ == 0)
{
lean_object* v___x_4007_; 
lean_dec(v_a_3995_);
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 0, v___x_4000_);
v___x_4007_ = v___x_3997_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4000_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
else
{
size_t v___x_4009_; lean_object* v___x_4010_; 
lean_del_object(v___x_3997_);
v___x_4009_ = lean_usize_of_nat(v___x_3999_);
v___x_4010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(v_a_3995_, v___x_3986_, v___x_4009_, v___x_4000_, v___y_3988_);
lean_dec(v_a_3995_);
return v___x_4010_;
}
}
else
{
size_t v___x_4011_; lean_object* v___x_4012_; 
lean_del_object(v___x_3997_);
v___x_4011_ = lean_usize_of_nat(v___x_3999_);
v___x_4012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(v_a_3995_, v___x_3986_, v___x_4011_, v___x_4000_, v___y_3988_);
lean_dec(v_a_3995_);
return v___x_4012_;
}
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
v_a_4014_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3994_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_3994_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v___x_4022_, lean_object* v___x_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
size_t v___x_8305__boxed_4031_; lean_object* v_res_4032_; 
v___x_8305__boxed_4031_ = lean_unbox_usize(v___x_4023_);
lean_dec(v___x_4023_);
v_res_4032_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(v___x_4022_, v___x_8305__boxed_4031_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___x_4022_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_as_4033_, size_t v_sz_4034_, size_t v_i_4035_, lean_object* v_b_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
uint8_t v___x_4043_; 
v___x_4043_ = lean_usize_dec_lt(v_i_4035_, v_sz_4034_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4044_; 
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v_b_4036_);
return v___x_4044_;
}
else
{
lean_object* v_maxSteps_4045_; lean_object* v_a_4046_; lean_object* v___x_4047_; 
v_maxSteps_4045_ = lean_ctor_get(v___y_4037_, 1);
v_a_4046_ = lean_array_uget_borrowed(v_as_4033_, v_i_4035_);
lean_inc(v_maxSteps_4045_);
lean_inc(v_a_4046_);
lean_inc(v_b_4036_);
v___x_4047_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta(v_b_4036_, v_a_4046_, v_maxSteps_4045_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v_a_4050_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref_known(v___x_4047_, 1);
if (lean_obj_tag(v_a_4048_) == 1)
{
lean_object* v_val_4054_; 
lean_dec(v_b_4036_);
v_val_4054_ = lean_ctor_get(v_a_4048_, 0);
lean_inc(v_val_4054_);
lean_dec_ref_known(v_a_4048_, 1);
v_a_4050_ = v_val_4054_;
goto v___jp_4049_;
}
else
{
lean_dec(v_a_4048_);
v_a_4050_ = v_b_4036_;
goto v___jp_4049_;
}
v___jp_4049_:
{
size_t v___x_4051_; size_t v___x_4052_; 
v___x_4051_ = ((size_t)1ULL);
v___x_4052_ = lean_usize_add(v_i_4035_, v___x_4051_);
v_i_4035_ = v___x_4052_;
v_b_4036_ = v_a_4050_;
goto _start;
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec(v_b_4036_);
v_a_4055_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4047_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4047_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_as_4063_, lean_object* v_sz_4064_, lean_object* v_i_4065_, lean_object* v_b_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
size_t v_sz_boxed_4073_; size_t v_i_boxed_4074_; lean_object* v_res_4075_; 
v_sz_boxed_4073_ = lean_unbox_usize(v_sz_4064_);
lean_dec(v_sz_4064_);
v_i_boxed_4074_ = lean_unbox_usize(v_i_4065_);
lean_dec(v_i_4065_);
v_res_4075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_as_4063_, v_sz_boxed_4073_, v_i_boxed_4074_, v_b_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec_ref(v_as_4063_);
return v_res_4075_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_m_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v_buckets_4078_; lean_object* v___x_4079_; uint64_t v___x_4080_; uint64_t v___x_4081_; uint64_t v___x_4082_; uint64_t v_fold_4083_; uint64_t v___x_4084_; uint64_t v___x_4085_; uint64_t v___x_4086_; size_t v___x_4087_; size_t v___x_4088_; size_t v___x_4089_; size_t v___x_4090_; size_t v___x_4091_; lean_object* v___x_4092_; uint8_t v___x_4093_; 
v_buckets_4078_ = lean_ctor_get(v_m_4076_, 1);
v___x_4079_ = lean_array_get_size(v_buckets_4078_);
v___x_4080_ = l_Lean_instHashableFVarId_hash(v_a_4077_);
v___x_4081_ = 32ULL;
v___x_4082_ = lean_uint64_shift_right(v___x_4080_, v___x_4081_);
v_fold_4083_ = lean_uint64_xor(v___x_4080_, v___x_4082_);
v___x_4084_ = 16ULL;
v___x_4085_ = lean_uint64_shift_right(v_fold_4083_, v___x_4084_);
v___x_4086_ = lean_uint64_xor(v_fold_4083_, v___x_4085_);
v___x_4087_ = lean_uint64_to_usize(v___x_4086_);
v___x_4088_ = lean_usize_of_nat(v___x_4079_);
v___x_4089_ = ((size_t)1ULL);
v___x_4090_ = lean_usize_sub(v___x_4088_, v___x_4089_);
v___x_4091_ = lean_usize_land(v___x_4087_, v___x_4090_);
v___x_4092_ = lean_array_uget_borrowed(v_buckets_4078_, v___x_4091_);
v___x_4093_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_4077_, v___x_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_m_4094_, lean_object* v_a_4095_){
_start:
{
uint8_t v_res_4096_; lean_object* v_r_4097_; 
v_res_4096_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_m_4094_, v_a_4095_);
lean_dec(v_a_4095_);
lean_dec_ref(v_m_4094_);
v_r_4097_ = lean_box(v_res_4096_);
return v_r_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg(lean_object* v_as_4098_, size_t v_i_4099_, size_t v_stop_4100_, lean_object* v_b_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_a_4105_; uint8_t v___x_4109_; 
v___x_4109_ = lean_usize_dec_eq(v_i_4099_, v_stop_4100_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; lean_object* v_acNfCache_4111_; lean_object* v___x_4112_; uint8_t v___x_4113_; 
v___x_4110_ = lean_st_ref_get(v___y_4102_);
v_acNfCache_4111_ = lean_ctor_get(v___x_4110_, 1);
lean_inc_ref(v_acNfCache_4111_);
lean_dec(v___x_4110_);
v___x_4112_ = lean_array_uget_borrowed(v_as_4098_, v_i_4099_);
v___x_4113_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_acNfCache_4111_, v___x_4112_);
lean_dec_ref(v_acNfCache_4111_);
if (v___x_4113_ == 0)
{
lean_object* v___x_4114_; 
lean_inc(v___x_4112_);
v___x_4114_ = lean_array_push(v_b_4101_, v___x_4112_);
v_a_4105_ = v___x_4114_;
goto v___jp_4104_;
}
else
{
v_a_4105_ = v_b_4101_;
goto v___jp_4104_;
}
}
else
{
lean_object* v___x_4115_; 
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v_b_4101_);
return v___x_4115_;
}
v___jp_4104_:
{
size_t v___x_4106_; size_t v___x_4107_; 
v___x_4106_ = ((size_t)1ULL);
v___x_4107_ = lean_usize_add(v_i_4099_, v___x_4106_);
v_i_4099_ = v___x_4107_;
v_b_4101_ = v_a_4105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg___boxed(lean_object* v_as_4116_, lean_object* v_i_4117_, lean_object* v_stop_4118_, lean_object* v_b_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
size_t v_i_boxed_4122_; size_t v_stop_boxed_4123_; lean_object* v_res_4124_; 
v_i_boxed_4122_ = lean_unbox_usize(v_i_4117_);
lean_dec(v_i_4117_);
v_stop_boxed_4123_ = lean_unbox_usize(v_stop_4118_);
lean_dec(v_stop_4118_);
v_res_4124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg(v_as_4116_, v_i_boxed_4122_, v_stop_boxed_4123_, v_b_4119_, v___y_4120_);
lean_dec(v___y_4120_);
lean_dec_ref(v_as_4116_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object* v_goal_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_Meta_getPropHyps(v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4142_; lean_object* v_a_4144_; lean_object* v___y_4177_; lean_object* v___x_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v___x_4142_ = lean_unsigned_to_nat(0u);
v___x_4187_ = lean_array_get_size(v_a_4141_);
v___x_4188_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__1));
v___x_4189_ = lean_nat_dec_lt(v___x_4142_, v___x_4187_);
if (v___x_4189_ == 0)
{
lean_dec(v_a_4141_);
v_a_4144_ = v___x_4188_;
goto v___jp_4143_;
}
else
{
uint8_t v___x_4190_; 
v___x_4190_ = lean_nat_dec_le(v___x_4187_, v___x_4187_);
if (v___x_4190_ == 0)
{
if (v___x_4189_ == 0)
{
lean_dec(v_a_4141_);
v_a_4144_ = v___x_4188_;
goto v___jp_4143_;
}
else
{
size_t v___x_4191_; size_t v___x_4192_; lean_object* v___x_4193_; 
v___x_4191_ = ((size_t)0ULL);
v___x_4192_ = lean_usize_of_nat(v___x_4187_);
v___x_4193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg(v_a_4141_, v___x_4191_, v___x_4192_, v___x_4188_, v___y_4134_);
lean_dec(v_a_4141_);
v___y_4177_ = v___x_4193_;
goto v___jp_4176_;
}
}
else
{
size_t v___x_4194_; size_t v___x_4195_; lean_object* v___x_4196_; 
v___x_4194_ = ((size_t)0ULL);
v___x_4195_ = lean_usize_of_nat(v___x_4187_);
v___x_4196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg(v_a_4141_, v___x_4194_, v___x_4195_, v___x_4188_, v___y_4134_);
lean_dec(v_a_4141_);
v___y_4177_ = v___x_4196_;
goto v___jp_4176_;
}
}
v___jp_4143_:
{
size_t v_sz_4145_; size_t v___x_4146_; lean_object* v___x_4147_; 
v_sz_4145_ = lean_array_size(v_a_4144_);
v___x_4146_ = ((size_t)0ULL);
v___x_4147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_a_4144_, v_sz_4145_, v___x_4146_, v_goal_4132_, v___y_4133_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec_ref(v_a_4144_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; lean_object* v___f_4149_; lean_object* v___x_4150_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc_n(v_a_4148_, 2);
lean_dec_ref_known(v___x_4147_, 1);
v___f_4149_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__0));
v___x_4150_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg(v_a_4148_, v___f_4149_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4158_; 
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4158_ == 0)
{
lean_object* v_unused_4159_; 
v_unused_4159_ = lean_ctor_get(v___x_4150_, 0);
lean_dec(v_unused_4159_);
v___x_4152_ = v___x_4150_;
v_isShared_4153_ = v_isSharedCheck_4158_;
goto v_resetjp_4151_;
}
else
{
lean_dec(v___x_4150_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4158_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4154_; lean_object* v___x_4156_; 
v___x_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4154_, 0, v_a_4148_);
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 0, v___x_4154_);
v___x_4156_ = v___x_4152_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v___x_4154_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
lean_dec(v_a_4148_);
v_a_4160_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4150_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4150_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
v_a_4168_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4147_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4147_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
v___jp_4176_:
{
if (lean_obj_tag(v___y_4177_) == 0)
{
lean_object* v_a_4178_; 
v_a_4178_ = lean_ctor_get(v___y_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v___y_4177_, 1);
v_a_4144_ = v_a_4178_;
goto v___jp_4143_;
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_dec(v_goal_4132_);
v_a_4179_ = lean_ctor_get(v___y_4177_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___y_4177_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___y_4177_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___y_4177_);
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
else
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
lean_dec(v_goal_4132_);
v_a_4197_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4199_ = v___x_4140_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4140_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v_goal_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(v_goal_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__2(lean_object* v_goal_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v___f_4222_; lean_object* v___x_4223_; 
lean_inc(v_goal_4214_);
v___f_4222_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4222_, 0, v_goal_4214_);
v___x_4223_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg(v_goal_4214_, v___f_4222_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__2___boxed(lean_object* v_goal_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
lean_object* v_res_4232_; 
v_res_4232_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__2(v_goal_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
return v_res_4232_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object* v_00_u03b2_4241_, lean_object* v_m_4242_, lean_object* v_a_4243_){
_start:
{
uint8_t v___x_4244_; 
v___x_4244_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_m_4242_, v_a_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_00_u03b2_4245_, lean_object* v_m_4246_, lean_object* v_a_4247_){
_start:
{
uint8_t v_res_4248_; lean_object* v_r_4249_; 
v_res_4248_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(v_00_u03b2_4245_, v_m_4246_, v_a_4247_);
lean_dec(v_a_4247_);
lean_dec_ref(v_m_4246_);
v_r_4249_ = lean_box(v_res_4248_);
return v_r_4249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object* v_00_u03b2_4250_, lean_object* v_m_4251_, lean_object* v_a_4252_, lean_object* v_b_4253_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_m_4251_, v_a_4252_, v_b_4253_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object* v_as_4255_, size_t v_sz_4256_, size_t v_i_4257_, lean_object* v_b_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v___x_4266_; 
v___x_4266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_as_4255_, v_sz_4256_, v_i_4257_, v_b_4258_, v___y_4259_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_as_4267_, lean_object* v_sz_4268_, lean_object* v_i_4269_, lean_object* v_b_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
size_t v_sz_boxed_4278_; size_t v_i_boxed_4279_; lean_object* v_res_4280_; 
v_sz_boxed_4278_ = lean_unbox_usize(v_sz_4268_);
lean_dec(v_sz_4268_);
v_i_boxed_4279_ = lean_unbox_usize(v_i_4269_);
lean_dec(v_i_4269_);
v_res_4280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(v_as_4267_, v_sz_boxed_4278_, v_i_boxed_4279_, v_b_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec_ref(v_as_4267_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3(lean_object* v_as_4281_, size_t v_i_4282_, size_t v_stop_4283_, lean_object* v_b_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(v_as_4281_, v_i_4282_, v_stop_4283_, v_b_4284_, v___y_4286_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___boxed(lean_object* v_as_4293_, lean_object* v_i_4294_, lean_object* v_stop_4295_, lean_object* v_b_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
size_t v_i_boxed_4304_; size_t v_stop_boxed_4305_; lean_object* v_res_4306_; 
v_i_boxed_4304_ = lean_unbox_usize(v_i_4294_);
lean_dec(v_i_4294_);
v_stop_boxed_4305_ = lean_unbox_usize(v_stop_4295_);
lean_dec(v_stop_4295_);
v_res_4306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3(v_as_4293_, v_i_boxed_4304_, v_stop_boxed_4305_, v_b_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec_ref(v_as_4293_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5(lean_object* v_as_4307_, size_t v_i_4308_, size_t v_stop_4309_, lean_object* v_b_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg(v_as_4307_, v_i_4308_, v_stop_4309_, v_b_4310_, v___y_4312_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___boxed(lean_object* v_as_4319_, lean_object* v_i_4320_, lean_object* v_stop_4321_, lean_object* v_b_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
size_t v_i_boxed_4330_; size_t v_stop_boxed_4331_; lean_object* v_res_4332_; 
v_i_boxed_4330_ = lean_unbox_usize(v_i_4320_);
lean_dec(v_i_4320_);
v_stop_boxed_4331_ = lean_unbox_usize(v_stop_4321_);
lean_dec(v_stop_4321_);
v_res_4332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5(v_as_4319_, v_i_boxed_4330_, v_stop_boxed_4331_, v_b_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec_ref(v_as_4319_);
return v_res_4332_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0(lean_object* v_00_u03b2_4333_, lean_object* v_a_4334_, lean_object* v_x_4335_){
_start:
{
uint8_t v___x_4336_; 
v___x_4336_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_4334_, v_x_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4337_, lean_object* v_a_4338_, lean_object* v_x_4339_){
_start:
{
uint8_t v_res_4340_; lean_object* v_r_4341_; 
v_res_4340_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0(v_00_u03b2_4337_, v_a_4338_, v_x_4339_);
lean_dec(v_x_4339_);
lean_dec(v_a_4338_);
v_r_4341_ = lean_box(v_res_4340_);
return v_r_4341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2(lean_object* v_00_u03b2_4342_, lean_object* v_data_4343_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(v_data_4343_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4345_, lean_object* v_i_4346_, lean_object* v_source_4347_, lean_object* v_target_4348_){
_start:
{
lean_object* v___x_4349_; 
v___x_4349_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(v_i_4346_, v_source_4347_, v_target_4348_);
return v___x_4349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4350_, lean_object* v_x_4351_, lean_object* v_x_4352_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(v_x_4351_, v_x_4352_);
return v___x_4353_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_AC_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_AC_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(builtin);
}
#ifdef __cplusplus
}
#endif
