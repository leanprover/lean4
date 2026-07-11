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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
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
lean_object* l_Lean_indentExpr(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Canonicalizing with respect to operation: '"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Operations mismatch:\n      the left-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n        "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\n      but the right-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to recognize operation: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___y_1250_ = v___y_1263_;
v___y_1251_ = v___y_1264_;
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
v___y_1250_ = v___y_1263_;
v___y_1251_ = v___y_1264_;
goto v___jp_1247_;
}
else
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = lean_usize_of_nat(v___x_1268_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1266_, v___x_1271_, v___x_1272_, v___y_1264_);
v___y_1248_ = v___y_1265_;
v_buckets_1249_ = v_buckets_1266_;
v___y_1250_ = v___y_1263_;
v___y_1251_ = v___x_1273_;
goto v___jp_1247_;
}
}
else
{
size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = lean_usize_of_nat(v___x_1268_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1266_, v___x_1274_, v___x_1275_, v___y_1264_);
v___y_1248_ = v___y_1265_;
v_buckets_1249_ = v_buckets_1266_;
v___y_1250_ = v___y_1263_;
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
v___y_1263_ = v_snd_1285_;
v___y_1264_ = v_fst_1283_;
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
v___y_1263_ = v_snd_1285_;
v___y_1264_ = v_fst_1283_;
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
v___y_1278_ = v_snd_1285_;
v___y_1279_ = v_fst_1283_;
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
v___y_1278_ = v_snd_1285_;
v___y_1279_ = v_fst_1283_;
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
v___x_1552_ = lean_nat_dec_le(v___y_1551_, v___y_1548_);
if (v___x_1552_ == 0)
{
lean_dec(v___y_1548_);
lean_inc(v___y_1551_);
v___y_1542_ = v___y_1551_;
v___y_1543_ = v___y_1549_;
v___y_1544_ = v___y_1550_;
v___y_1545_ = v___y_1551_;
goto v___jp_1541_;
}
else
{
v___y_1542_ = v___y_1551_;
v___y_1543_ = v___y_1549_;
v___y_1544_ = v___y_1550_;
v___y_1545_ = v___y_1548_;
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
v___y_1548_ = v___x_1559_;
v___y_1549_ = v___y_1554_;
v___y_1550_ = v___x_1555_;
v___y_1551_ = v___x_1559_;
goto v___jp_1547_;
}
else
{
v___y_1548_ = v___x_1559_;
v___y_1549_ = v___y_1554_;
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
uint8_t v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = l_Lean_Expr_hasMVar(v_e_1653_);
v___x_1657_ = lean_bool_not(v___x_1656_);
if (v___x_1657_ == 0)
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
else
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v_e_1653_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1679_, v___y_1680_);
lean_dec(v___y_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1683_, v___y_1685_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(v_e_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object* v_x_1697_, lean_object* v_y_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_Meta_mkEq(v_x_1697_, v_y_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1727_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1727_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1727_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set_tag(v___x_1707_, 1);
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = 0;
v___x_1712_ = lean_box(0);
v___x_1713_ = l_Lean_Meta_mkFreshExprMVar(v___x_1710_, v___x_1711_, v___x_1712_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1713_, 1);
v___x_1715_ = l_Lean_Expr_mvarId_x21(v_a_1714_);
v___x_1716_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1715_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v___x_1717_; 
lean_dec_ref_known(v___x_1716_, 1);
v___x_1717_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1714_, v_a_1700_);
return v___x_1717_;
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_a_1714_);
v_a_1718_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1716_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1716_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
return v___x_1713_;
}
}
}
}
else
{
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1728_, lean_object* v_y_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v_x_1728_, v_y_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
return v_res_1735_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_unsigned_to_nat(32u);
v___x_1737_ = lean_mk_empty_array_with_capacity(v___x_1736_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1739_ = ((size_t)5ULL);
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = lean_unsigned_to_nat(32u);
v___x_1742_ = lean_mk_empty_array_with_capacity(v___x_1741_);
v___x_1743_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1744_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v___x_1742_);
lean_ctor_set(v___x_1744_, 2, v___x_1740_);
lean_ctor_set(v___x_1744_, 3, v___x_1740_);
lean_ctor_set_usize(v___x_1744_, 4, v___x_1739_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; lean_object* v_traceState_1748_; lean_object* v_traces_1749_; lean_object* v___x_1750_; lean_object* v_traceState_1751_; lean_object* v_env_1752_; lean_object* v_nextMacroScope_1753_; lean_object* v_ngen_1754_; lean_object* v_auxDeclNGen_1755_; lean_object* v_cache_1756_; lean_object* v_messages_1757_; lean_object* v_infoState_1758_; lean_object* v_snapshotTasks_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1778_; 
v___x_1747_ = lean_st_ref_get(v___y_1745_);
v_traceState_1748_ = lean_ctor_get(v___x_1747_, 4);
lean_inc_ref(v_traceState_1748_);
lean_dec(v___x_1747_);
v_traces_1749_ = lean_ctor_get(v_traceState_1748_, 0);
lean_inc_ref(v_traces_1749_);
lean_dec_ref(v_traceState_1748_);
v___x_1750_ = lean_st_ref_take(v___y_1745_);
v_traceState_1751_ = lean_ctor_get(v___x_1750_, 4);
v_env_1752_ = lean_ctor_get(v___x_1750_, 0);
v_nextMacroScope_1753_ = lean_ctor_get(v___x_1750_, 1);
v_ngen_1754_ = lean_ctor_get(v___x_1750_, 2);
v_auxDeclNGen_1755_ = lean_ctor_get(v___x_1750_, 3);
v_cache_1756_ = lean_ctor_get(v___x_1750_, 5);
v_messages_1757_ = lean_ctor_get(v___x_1750_, 6);
v_infoState_1758_ = lean_ctor_get(v___x_1750_, 7);
v_snapshotTasks_1759_ = lean_ctor_get(v___x_1750_, 8);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1761_ = v___x_1750_;
v_isShared_1762_ = v_isSharedCheck_1778_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_snapshotTasks_1759_);
lean_inc(v_infoState_1758_);
lean_inc(v_messages_1757_);
lean_inc(v_cache_1756_);
lean_inc(v_traceState_1751_);
lean_inc(v_auxDeclNGen_1755_);
lean_inc(v_ngen_1754_);
lean_inc(v_nextMacroScope_1753_);
lean_inc(v_env_1752_);
lean_dec(v___x_1750_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1778_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
uint64_t v_tid_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1776_; 
v_tid_1763_ = lean_ctor_get_uint64(v_traceState_1751_, sizeof(void*)*1);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_traceState_1751_);
if (v_isSharedCheck_1776_ == 0)
{
lean_object* v_unused_1777_; 
v_unused_1777_ = lean_ctor_get(v_traceState_1751_, 0);
lean_dec(v_unused_1777_);
v___x_1765_ = v_traceState_1751_;
v_isShared_1766_ = v_isSharedCheck_1776_;
goto v_resetjp_1764_;
}
else
{
lean_dec(v_traceState_1751_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1776_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1767_);
v___x_1769_ = v___x_1765_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1767_);
lean_ctor_set_uint64(v_reuseFailAlloc_1775_, sizeof(void*)*1, v_tid_1763_);
v___x_1769_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1771_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 4, v___x_1769_);
v___x_1771_ = v___x_1761_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_env_1752_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_nextMacroScope_1753_);
lean_ctor_set(v_reuseFailAlloc_1774_, 2, v_ngen_1754_);
lean_ctor_set(v_reuseFailAlloc_1774_, 3, v_auxDeclNGen_1755_);
lean_ctor_set(v_reuseFailAlloc_1774_, 4, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1774_, 5, v_cache_1756_);
lean_ctor_set(v_reuseFailAlloc_1774_, 6, v_messages_1757_);
lean_ctor_set(v_reuseFailAlloc_1774_, 7, v_infoState_1758_);
lean_ctor_set(v_reuseFailAlloc_1774_, 8, v_snapshotTasks_1759_);
v___x_1771_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_st_ref_set(v___y_1745_, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v_traces_1749_);
return v___x_1773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1779_);
lean_dec(v___y_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
return v_res_1799_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1800_, lean_object* v_opt_1801_){
_start:
{
lean_object* v_name_1802_; lean_object* v_defValue_1803_; lean_object* v_map_1804_; lean_object* v___x_1805_; 
v_name_1802_ = lean_ctor_get(v_opt_1801_, 0);
v_defValue_1803_ = lean_ctor_get(v_opt_1801_, 1);
v_map_1804_ = lean_ctor_get(v_opts_1800_, 0);
v___x_1805_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1804_, v_name_1802_);
if (lean_obj_tag(v___x_1805_) == 0)
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_unbox(v_defValue_1803_);
return v___x_1806_;
}
else
{
lean_object* v_val_1807_; 
v_val_1807_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_val_1807_);
lean_dec_ref_known(v___x_1805_, 1);
if (lean_obj_tag(v_val_1807_) == 1)
{
uint8_t v_v_1808_; 
v_v_1808_ = lean_ctor_get_uint8(v_val_1807_, 0);
lean_dec_ref_known(v_val_1807_, 0);
return v_v_1808_;
}
else
{
uint8_t v___x_1809_; 
lean_dec(v_val_1807_);
v___x_1809_ = lean_unbox(v_defValue_1803_);
return v___x_1809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1810_, lean_object* v_opt_1811_){
_start:
{
uint8_t v_res_1812_; lean_object* v_r_1813_; 
v_res_1812_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_1810_, v_opt_1811_);
lean_dec_ref(v_opt_1811_);
lean_dec_ref(v_opts_1810_);
v_r_1813_ = lean_box(v_res_1812_);
return v_r_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1814_, lean_object* v_____do__lift_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_options_1824_; uint8_t v_hasTrace_1825_; 
v_options_1824_ = lean_ctor_get(v___y_1821_, 2);
v_hasTrace_1825_ = lean_ctor_get_uint8(v_options_1824_, sizeof(void*)*1);
if (v_hasTrace_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec(v_cls_1814_);
v___x_1826_ = lean_box(v_hasTrace_1825_);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1828_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1829_ = l_Lean_Name_append(v___x_1828_, v_cls_1814_);
v___x_1830_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1815_, v_options_1824_, v___x_1829_);
lean_dec(v___x_1829_);
v___x_1831_ = lean_box(v___x_1830_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1833_, lean_object* v_____do__lift_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_1833_, v_____do__lift_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v_____do__lift_1834_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_mkAppB(v___x_1844_, v___y_1845_, v___y_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1848_, lean_object* v_lhs_1849_, lean_object* v_rhs_1850_, lean_object* v_P_1851_, uint8_t v___x_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___x_1859_; 
lean_inc_ref(v_lhs_1849_);
lean_inc_ref(v_val_1848_);
v___x_1859_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1848_, v_lhs_1849_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v_fst_1861_; lean_object* v_snd_1862_; lean_object* v___x_1863_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v___x_1859_, 1);
v_fst_1861_ = lean_ctor_get(v_a_1860_, 0);
lean_inc(v_fst_1861_);
v_snd_1862_ = lean_ctor_get(v_a_1860_, 1);
lean_inc(v_snd_1862_);
lean_dec(v_a_1860_);
lean_inc_ref(v_rhs_1850_);
lean_inc_ref(v_val_1848_);
v___x_1863_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1848_, v_rhs_1850_, v_snd_1862_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v_fst_1865_; lean_object* v_snd_1866_; lean_object* v___x_1867_; lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1958_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v_fst_1865_ = lean_ctor_get(v_a_1864_, 0);
lean_inc(v_fst_1865_);
v_snd_1866_ = lean_ctor_get(v_a_1864_, 1);
lean_inc(v_snd_1866_);
lean_dec(v_a_1864_);
v___x_1867_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_1861_, v_fst_1865_, v_snd_1866_);
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1958_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1958_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v_fst_1872_; lean_object* v_snd_1873_; lean_object* v_common_1874_; lean_object* v_x_1875_; lean_object* v_y_1876_; lean_object* v___x_1877_; 
v_fst_1872_ = lean_ctor_get(v_a_1868_, 0);
lean_inc(v_fst_1872_);
v_snd_1873_ = lean_ctor_get(v_a_1868_, 1);
lean_inc(v_snd_1873_);
lean_dec(v_a_1868_);
v_common_1874_ = lean_ctor_get(v_fst_1872_, 0);
lean_inc_ref(v_common_1874_);
v_x_1875_ = lean_ctor_get(v_fst_1872_, 1);
lean_inc_ref(v_x_1875_);
v_y_1876_ = lean_ctor_get(v_fst_1872_, 2);
lean_inc_ref(v_y_1876_);
lean_dec(v_fst_1872_);
lean_inc_ref(v_val_1848_);
v___x_1877_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_1874_, v_val_1848_, v_snd_1873_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec_ref(v_common_1874_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v_fst_1879_; lean_object* v_snd_1880_; lean_object* v___x_1881_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v_fst_1879_ = lean_ctor_get(v_a_1878_, 0);
lean_inc(v_fst_1879_);
v_snd_1880_ = lean_ctor_get(v_a_1878_, 1);
lean_inc(v_snd_1880_);
lean_dec(v_a_1878_);
lean_inc_ref(v_val_1848_);
v___x_1881_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_1875_, v_val_1848_, v_snd_1880_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec_ref(v_x_1875_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v_fst_1883_; lean_object* v_snd_1884_; lean_object* v___x_1885_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v_fst_1883_ = lean_ctor_get(v_a_1882_, 0);
lean_inc(v_fst_1883_);
v_snd_1884_ = lean_ctor_get(v_a_1882_, 1);
lean_inc(v_snd_1884_);
lean_dec(v_a_1882_);
lean_inc_ref(v_val_1848_);
v___x_1885_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_1876_, v_val_1848_, v_snd_1884_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec_ref(v_y_1876_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v_fst_1887_; lean_object* v_snd_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1933_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v_fst_1887_ = lean_ctor_get(v_a_1886_, 0);
v_snd_1888_ = lean_ctor_get(v_a_1886_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_a_1886_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1890_ = v_a_1886_;
v_isShared_1891_ = v_isSharedCheck_1933_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_snd_1888_);
lean_inc(v_fst_1887_);
lean_dec(v_a_1886_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1933_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___x_1923_; lean_object* v___f_1924_; lean_object* v___y_1926_; lean_object* v___x_1930_; 
lean_inc_ref(v_val_1848_);
v___x_1923_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_1848_);
v___f_1924_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_1924_, 0, v___x_1923_);
lean_inc(v_fst_1879_);
lean_inc_ref(v___f_1924_);
v___x_1930_ = l_Option_merge___redArg(v___f_1924_, v_fst_1879_, v_fst_1883_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v___x_1931_; 
lean_inc_ref(v_val_1848_);
v___x_1931_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1848_);
v___y_1926_ = v___x_1931_;
goto v___jp_1925_;
}
else
{
lean_object* v_val_1932_; 
v_val_1932_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_val_1932_);
lean_dec_ref_known(v___x_1930_, 1);
v___y_1926_ = v_val_1932_;
goto v___jp_1925_;
}
v___jp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_inc_ref(v_P_1851_);
v___x_1895_ = l_Lean_mkAppB(v_P_1851_, v_lhs_1849_, v_rhs_1850_);
v___x_1896_ = l_Lean_mkAppB(v_P_1851_, v___y_1893_, v___y_1894_);
lean_inc_ref(v___x_1896_);
v___x_1897_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_1895_, v___x_1896_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1914_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1914_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1914_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set_tag(v___x_1870_, 1);
lean_ctor_set(v___x_1870_, 0, v_a_1898_);
v___x_1903_ = v___x_1870_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1904_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1904_, 0, v___x_1896_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
lean_ctor_set_uint8(v___x_1904_, sizeof(void*)*2, v___x_1852_);
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1906_);
v___x_1908_ = v___x_1890_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_snd_1888_);
v___x_1908_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1910_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1908_);
v___x_1910_ = v___x_1900_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec_ref(v___x_1896_);
lean_del_object(v___x_1890_);
lean_dec(v_snd_1888_);
lean_del_object(v___x_1870_);
v_a_1915_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1897_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1897_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
v___jp_1925_:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Option_merge___redArg(v___f_1924_, v_fst_1879_, v_fst_1887_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1848_);
v___y_1893_ = v___y_1926_;
v___y_1894_ = v___x_1928_;
goto v___jp_1892_;
}
else
{
lean_object* v_val_1929_; 
lean_dec_ref(v_val_1848_);
v_val_1929_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_val_1929_);
lean_dec_ref_known(v___x_1927_, 1);
v___y_1893_ = v___y_1926_;
v___y_1894_ = v_val_1929_;
goto v___jp_1892_;
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec(v_fst_1883_);
lean_dec(v_fst_1879_);
lean_del_object(v___x_1870_);
lean_dec_ref(v_P_1851_);
lean_dec_ref(v_rhs_1850_);
lean_dec_ref(v_lhs_1849_);
lean_dec_ref(v_val_1848_);
v_a_1934_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1885_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1885_);
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
lean_dec(v_fst_1879_);
lean_dec_ref(v_y_1876_);
lean_del_object(v___x_1870_);
lean_dec_ref(v_P_1851_);
lean_dec_ref(v_rhs_1850_);
lean_dec_ref(v_lhs_1849_);
lean_dec_ref(v_val_1848_);
v_a_1942_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1881_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1881_);
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
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v_y_1876_);
lean_dec_ref(v_x_1875_);
lean_del_object(v___x_1870_);
lean_dec_ref(v_P_1851_);
lean_dec_ref(v_rhs_1850_);
lean_dec_ref(v_lhs_1849_);
lean_dec_ref(v_val_1848_);
v_a_1950_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1877_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1877_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v_fst_1861_);
lean_dec_ref(v_P_1851_);
lean_dec_ref(v_rhs_1850_);
lean_dec_ref(v_lhs_1849_);
lean_dec_ref(v_val_1848_);
v_a_1959_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1863_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1863_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec_ref(v_P_1851_);
lean_dec_ref(v_rhs_1850_);
lean_dec_ref(v_lhs_1849_);
lean_dec_ref(v_val_1848_);
v_a_1967_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1859_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1859_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_1975_, lean_object* v_lhs_1976_, lean_object* v_rhs_1977_, lean_object* v_P_1978_, lean_object* v___x_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
uint8_t v___x_116334__boxed_1986_; lean_object* v_res_1987_; 
v___x_116334__boxed_1986_ = lean_unbox(v___x_1979_);
v_res_1987_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(v_val_1975_, v_lhs_1976_, v_rhs_1977_, v_P_1978_, v___x_116334__boxed_1986_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
return v_res_1987_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_1990_ = l_Lean_stringToMessageData(v___x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(v_x_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v_x_2002_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2012_, lean_object* v_msg_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_ref_2019_; lean_object* v___x_2020_; lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2065_; 
v_ref_2019_ = lean_ctor_get(v___y_2016_, 5);
v___x_2020_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2065_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2065_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v_traceState_2026_; lean_object* v_env_2027_; lean_object* v_nextMacroScope_2028_; lean_object* v_ngen_2029_; lean_object* v_auxDeclNGen_2030_; lean_object* v_cache_2031_; lean_object* v_messages_2032_; lean_object* v_infoState_2033_; lean_object* v_snapshotTasks_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2064_; 
v___x_2025_ = lean_st_ref_take(v___y_2017_);
v_traceState_2026_ = lean_ctor_get(v___x_2025_, 4);
v_env_2027_ = lean_ctor_get(v___x_2025_, 0);
v_nextMacroScope_2028_ = lean_ctor_get(v___x_2025_, 1);
v_ngen_2029_ = lean_ctor_get(v___x_2025_, 2);
v_auxDeclNGen_2030_ = lean_ctor_get(v___x_2025_, 3);
v_cache_2031_ = lean_ctor_get(v___x_2025_, 5);
v_messages_2032_ = lean_ctor_get(v___x_2025_, 6);
v_infoState_2033_ = lean_ctor_get(v___x_2025_, 7);
v_snapshotTasks_2034_ = lean_ctor_get(v___x_2025_, 8);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2036_ = v___x_2025_;
v_isShared_2037_ = v_isSharedCheck_2064_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_snapshotTasks_2034_);
lean_inc(v_infoState_2033_);
lean_inc(v_messages_2032_);
lean_inc(v_cache_2031_);
lean_inc(v_traceState_2026_);
lean_inc(v_auxDeclNGen_2030_);
lean_inc(v_ngen_2029_);
lean_inc(v_nextMacroScope_2028_);
lean_inc(v_env_2027_);
lean_dec(v___x_2025_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2064_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
uint64_t v_tid_2038_; lean_object* v_traces_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2063_; 
v_tid_2038_ = lean_ctor_get_uint64(v_traceState_2026_, sizeof(void*)*1);
v_traces_2039_ = lean_ctor_get(v_traceState_2026_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_traceState_2026_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2041_ = v_traceState_2026_;
v_isShared_2042_ = v_isSharedCheck_2063_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_traces_2039_);
lean_dec(v_traceState_2026_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2063_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; double v___x_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
v___x_2045_ = 0;
v___x_2046_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
v___x_2047_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2047_, 0, v_cls_2012_);
lean_ctor_set(v___x_2047_, 1, v___x_2043_);
lean_ctor_set(v___x_2047_, 2, v___x_2046_);
lean_ctor_set_float(v___x_2047_, sizeof(void*)*3, v___x_2044_);
lean_ctor_set_float(v___x_2047_, sizeof(void*)*3 + 8, v___x_2044_);
lean_ctor_set_uint8(v___x_2047_, sizeof(void*)*3 + 16, v___x_2045_);
v___x_2048_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__2));
v___x_2049_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set(v___x_2049_, 1, v_a_2021_);
lean_ctor_set(v___x_2049_, 2, v___x_2048_);
lean_inc(v_ref_2019_);
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_ref_2019_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = l_Lean_PersistentArray_push___redArg(v_traces_2039_, v___x_2050_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2051_);
v___x_2053_ = v___x_2041_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2051_);
lean_ctor_set_uint64(v_reuseFailAlloc_2062_, sizeof(void*)*1, v_tid_2038_);
v___x_2053_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2055_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 4, v___x_2053_);
v___x_2055_ = v___x_2036_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_env_2027_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_nextMacroScope_2028_);
lean_ctor_set(v_reuseFailAlloc_2061_, 2, v_ngen_2029_);
lean_ctor_set(v_reuseFailAlloc_2061_, 3, v_auxDeclNGen_2030_);
lean_ctor_set(v_reuseFailAlloc_2061_, 4, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2061_, 5, v_cache_2031_);
lean_ctor_set(v_reuseFailAlloc_2061_, 6, v_messages_2032_);
lean_ctor_set(v_reuseFailAlloc_2061_, 7, v_infoState_2033_);
lean_ctor_set(v_reuseFailAlloc_2061_, 8, v_snapshotTasks_2034_);
v___x_2055_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2056_ = lean_st_ref_set(v___y_2017_, v___x_2055_);
v___x_2057_ = lean_box(0);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2057_);
v___x_2059_ = v___x_2023_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2066_, lean_object* v_msg_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2066_, v_msg_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
return v_res_2073_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_unsigned_to_nat(16u);
v___x_2078_ = lean_mk_array(v___x_2077_, v___x_2076_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4));
v___x_2086_ = l_Lean_stringToMessageData(v___x_2085_);
return v___x_2086_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6));
v___x_2089_ = l_Lean_stringToMessageData(v___x_2088_);
return v___x_2089_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2092_ = l_Lean_stringToMessageData(v___x_2091_);
return v___x_2092_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10));
v___x_2095_ = l_Lean_stringToMessageData(v___x_2094_);
return v___x_2095_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12));
v___x_2098_ = l_Lean_stringToMessageData(v___x_2097_);
return v___x_2098_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14));
v___x_2101_ = l_Lean_stringToMessageData(v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object* v_lhs_2102_, lean_object* v_rhs_2103_, lean_object* v_P_2104_, lean_object* v_cls_2105_, lean_object* v___f_2106_, lean_object* v_____r_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v___x_2125_; 
lean_inc_ref(v_lhs_2102_);
v___x_2125_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2102_);
if (lean_obj_tag(v___x_2125_) == 1)
{
lean_object* v_val_2126_; lean_object* v___x_2127_; 
v_val_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_val_2126_);
lean_dec_ref_known(v___x_2125_, 1);
lean_inc_ref(v_rhs_2103_);
v___x_2127_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2103_);
if (lean_obj_tag(v___x_2127_) == 1)
{
lean_object* v_val_2128_; uint8_t v___x_2129_; uint8_t v___x_2130_; 
v_val_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_val_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v___x_2129_ = lean_expr_eqv(v_val_2126_, v_val_2128_);
v___x_2130_ = lean_bool_not(v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v_options_2131_; lean_object* v_inheritedTraceOptions_2132_; uint8_t v_hasTrace_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___f_2136_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; 
lean_dec(v_val_2128_);
lean_dec_ref(v___f_2106_);
v_options_2131_ = lean_ctor_get(v___y_2113_, 2);
v_inheritedTraceOptions_2132_ = lean_ctor_get(v___y_2113_, 13);
v_hasTrace_2133_ = lean_ctor_get_uint8(v_options_2131_, sizeof(void*)*1);
v___x_2134_ = 1;
v___x_2135_ = lean_box(v___x_2134_);
lean_inc(v_val_2126_);
v___f_2136_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 11, 5);
lean_closure_set(v___f_2136_, 0, v_val_2126_);
lean_closure_set(v___f_2136_, 1, v_lhs_2102_);
lean_closure_set(v___f_2136_, 2, v_rhs_2103_);
lean_closure_set(v___f_2136_, 3, v_P_2104_);
lean_closure_set(v___f_2136_, 4, v___x_2135_);
if (v_hasTrace_2133_ == 0)
{
lean_dec(v_cls_2105_);
v___y_2138_ = v___y_2111_;
v___y_2139_ = v___y_2112_;
v___y_2140_ = v___y_2113_;
v___y_2141_ = v___y_2114_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2105_);
v___x_2147_ = l_Lean_Name_append(v___x_2146_, v_cls_2105_);
v___x_2148_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2132_, v_options_2131_, v___x_2147_);
lean_dec(v___x_2147_);
if (v___x_2148_ == 0)
{
lean_dec(v_cls_2105_);
v___y_2138_ = v___y_2111_;
v___y_2139_ = v___y_2112_;
v___y_2140_ = v___y_2113_;
v___y_2141_ = v___y_2114_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2149_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
lean_inc(v_val_2126_);
v___x_2150_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2126_);
v___x_2151_ = l_Lean_MessageData_ofExpr(v___x_2150_);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2149_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2105_, v___x_2154_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_dec_ref_known(v___x_2155_, 1);
v___y_2138_ = v___y_2111_;
v___y_2139_ = v___y_2112_;
v___y_2140_ = v___y_2113_;
v___y_2141_ = v___y_2114_;
goto v___jp_2137_;
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec_ref(v___f_2136_);
lean_dec(v_val_2126_);
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
v___jp_2137_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2142_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2);
v___x_2143_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3));
v___x_2144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2144_, 0, v_val_2126_);
lean_ctor_set(v___x_2144_, 1, v___x_2142_);
lean_ctor_set(v___x_2144_, 2, v___x_2143_);
v___x_2145_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2136_, v___x_2144_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
return v___x_2145_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2164_; lean_object* v___x_2165_; 
lean_dec_ref(v_P_2104_);
v_inheritedTraceOptions_2164_ = lean_ctor_get(v___y_2113_, 13);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v_inheritedTraceOptions_2164_);
v___x_2165_ = lean_apply_9(v___f_2106_, v_inheritedTraceOptions_2164_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, lean_box(0));
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; uint8_t v___x_2167_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
v___x_2167_ = lean_unbox(v_a_2166_);
lean_dec(v_a_2166_);
if (v___x_2167_ == 0)
{
lean_dec(v_val_2128_);
lean_dec(v_val_2126_);
lean_dec(v_cls_2105_);
lean_dec_ref(v_rhs_2103_);
lean_dec_ref(v_lhs_2102_);
goto v___jp_2116_;
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2168_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9);
v___x_2169_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2126_);
v___x_2170_ = l_Lean_MessageData_ofExpr(v___x_2169_);
v___x_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2168_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11);
v___x_2173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2171_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
v___x_2174_ = l_Lean_indentExpr(v_lhs_2102_);
v___x_2175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2173_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13);
v___x_2177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2128_);
v___x_2179_ = l_Lean_MessageData_ofExpr(v___x_2178_);
v___x_2180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2177_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
lean_ctor_set(v___x_2181_, 1, v___x_2172_);
v___x_2182_ = l_Lean_indentExpr(v_rhs_2103_);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2105_, v___x_2183_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_dec_ref_known(v___x_2184_, 1);
goto v___jp_2116_;
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v_val_2128_);
lean_dec(v_val_2126_);
lean_dec(v_cls_2105_);
lean_dec_ref(v_rhs_2103_);
lean_dec_ref(v_lhs_2102_);
v_a_2193_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2165_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2165_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
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
else
{
lean_object* v_inheritedTraceOptions_2201_; lean_object* v___x_2202_; 
lean_dec(v___x_2127_);
lean_dec(v_val_2126_);
lean_dec_ref(v_P_2104_);
lean_dec_ref(v_lhs_2102_);
v_inheritedTraceOptions_2201_ = lean_ctor_get(v___y_2113_, 13);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v_inheritedTraceOptions_2201_);
v___x_2202_ = lean_apply_9(v___f_2106_, v_inheritedTraceOptions_2201_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, lean_box(0));
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; uint8_t v___x_2204_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___x_2204_ = lean_unbox(v_a_2203_);
lean_dec(v_a_2203_);
if (v___x_2204_ == 0)
{
lean_dec(v_cls_2105_);
lean_dec_ref(v_rhs_2103_);
goto v___jp_2119_;
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2206_ = l_Lean_indentExpr(v_rhs_2103_);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2105_, v___x_2207_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_dec_ref_known(v___x_2208_, 1);
goto v___jp_2119_;
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2208_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_cls_2105_);
lean_dec_ref(v_rhs_2103_);
v_a_2217_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2202_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2202_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2225_; lean_object* v___x_2226_; 
lean_dec(v___x_2125_);
lean_dec_ref(v_P_2104_);
lean_dec_ref(v_rhs_2103_);
v_inheritedTraceOptions_2225_ = lean_ctor_get(v___y_2113_, 13);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v_inheritedTraceOptions_2225_);
v___x_2226_ = lean_apply_9(v___f_2106_, v_inheritedTraceOptions_2225_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, lean_box(0));
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; uint8_t v___x_2228_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v___x_2228_ = lean_unbox(v_a_2227_);
lean_dec(v_a_2227_);
if (v___x_2228_ == 0)
{
lean_dec(v_cls_2105_);
lean_dec_ref(v_lhs_2102_);
goto v___jp_2122_;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2229_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2230_ = l_Lean_indentExpr(v_lhs_2102_);
v___x_2231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2229_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
v___x_2232_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2105_, v___x_2231_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_dec_ref_known(v___x_2232_, 1);
goto v___jp_2122_;
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v_cls_2105_);
lean_dec_ref(v_lhs_2102_);
v_a_2241_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2226_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2226_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
v___jp_2116_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
v___jp_2119_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
v___jp_2122_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object* v_lhs_2249_, lean_object* v_rhs_2250_, lean_object* v_P_2251_, lean_object* v_cls_2252_, lean_object* v___f_2253_, lean_object* v_____r_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2249_, v_rhs_2250_, v_P_2251_, v_cls_2252_, v___f_2253_, v_____r_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(lean_object* v_lhs_2264_, lean_object* v_rhs_2265_, lean_object* v_P_2266_, uint8_t v___x_2267_, lean_object* v_cls_2268_, lean_object* v___f_2269_, lean_object* v_____r_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2288_; 
lean_inc_ref(v_lhs_2264_);
v___x_2288_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2264_);
if (lean_obj_tag(v___x_2288_) == 1)
{
lean_object* v_val_2289_; lean_object* v___x_2290_; 
v_val_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_val_2289_);
lean_dec_ref_known(v___x_2288_, 1);
lean_inc_ref(v_rhs_2265_);
v___x_2290_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2265_);
if (lean_obj_tag(v___x_2290_) == 1)
{
lean_object* v_val_2291_; uint8_t v___x_2292_; uint8_t v___x_2293_; 
v_val_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_val_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2292_ = lean_expr_eqv(v_val_2289_, v_val_2291_);
v___x_2293_ = lean_bool_not(v___x_2292_);
if (v___x_2293_ == 0)
{
lean_object* v_options_2294_; lean_object* v_inheritedTraceOptions_2295_; uint8_t v_hasTrace_2296_; lean_object* v___x_2297_; lean_object* v___f_2298_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; 
lean_dec(v_val_2291_);
lean_dec_ref(v___f_2269_);
v_options_2294_ = lean_ctor_get(v___y_2276_, 2);
v_inheritedTraceOptions_2295_ = lean_ctor_get(v___y_2276_, 13);
v_hasTrace_2296_ = lean_ctor_get_uint8(v_options_2294_, sizeof(void*)*1);
v___x_2297_ = lean_box(v___x_2267_);
lean_inc(v_val_2289_);
v___f_2298_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 11, 5);
lean_closure_set(v___f_2298_, 0, v_val_2289_);
lean_closure_set(v___f_2298_, 1, v_lhs_2264_);
lean_closure_set(v___f_2298_, 2, v_rhs_2265_);
lean_closure_set(v___f_2298_, 3, v_P_2266_);
lean_closure_set(v___f_2298_, 4, v___x_2297_);
if (v_hasTrace_2296_ == 0)
{
lean_dec(v_cls_2268_);
v___y_2300_ = v___y_2274_;
v___y_2301_ = v___y_2275_;
v___y_2302_ = v___y_2276_;
v___y_2303_ = v___y_2277_;
goto v___jp_2299_;
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2268_);
v___x_2309_ = l_Lean_Name_append(v___x_2308_, v_cls_2268_);
v___x_2310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2295_, v_options_2294_, v___x_2309_);
lean_dec(v___x_2309_);
if (v___x_2310_ == 0)
{
lean_dec(v_cls_2268_);
v___y_2300_ = v___y_2274_;
v___y_2301_ = v___y_2275_;
v___y_2302_ = v___y_2276_;
v___y_2303_ = v___y_2277_;
goto v___jp_2299_;
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2311_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
lean_inc(v_val_2289_);
v___x_2312_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2289_);
v___x_2313_ = l_Lean_MessageData_ofExpr(v___x_2312_);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2311_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2268_, v___x_2316_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_dec_ref_known(v___x_2317_, 1);
v___y_2300_ = v___y_2274_;
v___y_2301_ = v___y_2275_;
v___y_2302_ = v___y_2276_;
v___y_2303_ = v___y_2277_;
goto v___jp_2299_;
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v___f_2298_);
lean_dec(v_val_2289_);
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
v___jp_2299_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2304_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2);
v___x_2305_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3));
v___x_2306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2306_, 0, v_val_2289_);
lean_ctor_set(v___x_2306_, 1, v___x_2304_);
lean_ctor_set(v___x_2306_, 2, v___x_2305_);
v___x_2307_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2298_, v___x_2306_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
return v___x_2307_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2326_; lean_object* v___x_2327_; 
lean_dec_ref(v_P_2266_);
v_inheritedTraceOptions_2326_ = lean_ctor_get(v___y_2276_, 13);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
lean_inc(v___y_2273_);
lean_inc_ref(v___y_2272_);
lean_inc(v___y_2271_);
lean_inc_ref(v_inheritedTraceOptions_2326_);
v___x_2327_ = lean_apply_9(v___f_2269_, v_inheritedTraceOptions_2326_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, lean_box(0));
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; uint8_t v___x_2329_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = lean_unbox(v_a_2328_);
lean_dec(v_a_2328_);
if (v___x_2329_ == 0)
{
lean_dec(v_val_2291_);
lean_dec(v_val_2289_);
lean_dec(v_cls_2268_);
lean_dec_ref(v_rhs_2265_);
lean_dec_ref(v_lhs_2264_);
goto v___jp_2279_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2330_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9);
v___x_2331_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2289_);
v___x_2332_ = l_Lean_MessageData_ofExpr(v___x_2331_);
v___x_2333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2330_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11);
v___x_2335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = l_Lean_indentExpr(v_lhs_2264_);
v___x_2337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13);
v___x_2339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2337_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2291_);
v___x_2341_ = l_Lean_MessageData_ofExpr(v___x_2340_);
v___x_2342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2339_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v___x_2334_);
v___x_2344_ = l_Lean_indentExpr(v_rhs_2265_);
v___x_2345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2268_, v___x_2345_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_dec_ref_known(v___x_2346_, 1);
goto v___jp_2279_;
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec(v_val_2291_);
lean_dec(v_val_2289_);
lean_dec(v_cls_2268_);
lean_dec_ref(v_rhs_2265_);
lean_dec_ref(v_lhs_2264_);
v_a_2355_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2327_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2327_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2363_; lean_object* v___x_2364_; 
lean_dec(v___x_2290_);
lean_dec(v_val_2289_);
lean_dec_ref(v_P_2266_);
lean_dec_ref(v_lhs_2264_);
v_inheritedTraceOptions_2363_ = lean_ctor_get(v___y_2276_, 13);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
lean_inc(v___y_2273_);
lean_inc_ref(v___y_2272_);
lean_inc(v___y_2271_);
lean_inc_ref(v_inheritedTraceOptions_2363_);
v___x_2364_ = lean_apply_9(v___f_2269_, v_inheritedTraceOptions_2363_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, lean_box(0));
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; uint8_t v___x_2366_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = lean_unbox(v_a_2365_);
lean_dec(v_a_2365_);
if (v___x_2366_ == 0)
{
lean_dec(v_cls_2268_);
lean_dec_ref(v_rhs_2265_);
goto v___jp_2282_;
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2367_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2368_ = l_Lean_indentExpr(v_rhs_2265_);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2268_, v___x_2369_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_dec_ref_known(v___x_2370_, 1);
goto v___jp_2282_;
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v_cls_2268_);
lean_dec_ref(v_rhs_2265_);
v_a_2379_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2364_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2364_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2387_; lean_object* v___x_2388_; 
lean_dec(v___x_2288_);
lean_dec_ref(v_P_2266_);
lean_dec_ref(v_rhs_2265_);
v_inheritedTraceOptions_2387_ = lean_ctor_get(v___y_2276_, 13);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
lean_inc(v___y_2273_);
lean_inc_ref(v___y_2272_);
lean_inc(v___y_2271_);
lean_inc_ref(v_inheritedTraceOptions_2387_);
v___x_2388_ = lean_apply_9(v___f_2269_, v_inheritedTraceOptions_2387_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, lean_box(0));
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; uint8_t v___x_2390_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = lean_unbox(v_a_2389_);
lean_dec(v_a_2389_);
if (v___x_2390_ == 0)
{
lean_dec(v_cls_2268_);
lean_dec_ref(v_lhs_2264_);
goto v___jp_2285_;
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2391_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2392_ = l_Lean_indentExpr(v_lhs_2264_);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2268_, v___x_2393_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_dec_ref_known(v___x_2394_, 1);
goto v___jp_2285_;
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec(v_cls_2268_);
lean_dec_ref(v_lhs_2264_);
v_a_2403_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2388_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2388_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
v___jp_2279_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
return v___x_2281_;
}
v___jp_2282_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
v___jp_2285_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7___boxed(lean_object* v_lhs_2411_, lean_object* v_rhs_2412_, lean_object* v_P_2413_, lean_object* v___x_2414_, lean_object* v_cls_2415_, lean_object* v___f_2416_, lean_object* v_____r_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
uint8_t v___x_117145__boxed_2426_; lean_object* v_res_2427_; 
v___x_117145__boxed_2426_ = lean_unbox(v___x_2414_);
v_res_2427_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(v_lhs_2411_, v_rhs_2412_, v_P_2413_, v___x_117145__boxed_2426_, v_cls_2415_, v___f_2416_, v_____r_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_x_2428_){
_start:
{
if (lean_obj_tag(v_x_2428_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
v_a_2430_ = lean_ctor_get(v_x_2428_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_x_2428_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v_x_2428_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v_x_2428_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set_tag(v___x_2432_, 1);
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
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
v_a_2438_ = lean_ctor_get(v_x_2428_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_x_2428_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v_x_2428_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v_x_2428_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set_tag(v___x_2440_, 0);
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_x_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_2446_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2449_, lean_object* v_opt_2450_){
_start:
{
lean_object* v_name_2451_; lean_object* v_defValue_2452_; lean_object* v_map_2453_; lean_object* v___x_2454_; 
v_name_2451_ = lean_ctor_get(v_opt_2450_, 0);
v_defValue_2452_ = lean_ctor_get(v_opt_2450_, 1);
v_map_2453_ = lean_ctor_get(v_opts_2449_, 0);
v___x_2454_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2453_, v_name_2451_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_inc(v_defValue_2452_);
return v_defValue_2452_;
}
else
{
lean_object* v_val_2455_; 
v_val_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_val_2455_);
lean_dec_ref_known(v___x_2454_, 1);
if (lean_obj_tag(v_val_2455_) == 3)
{
lean_object* v_v_2456_; 
v_v_2456_ = lean_ctor_get(v_val_2455_, 0);
lean_inc(v_v_2456_);
lean_dec_ref_known(v_val_2455_, 1);
return v_v_2456_;
}
else
{
lean_dec(v_val_2455_);
lean_inc(v_defValue_2452_);
return v_defValue_2452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2457_, lean_object* v_opt_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2457_, v_opt_2458_);
lean_dec_ref(v_opt_2458_);
lean_dec_ref(v_opts_2457_);
return v_res_2459_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_e_2460_){
_start:
{
if (lean_obj_tag(v_e_2460_) == 0)
{
uint8_t v___x_2461_; 
v___x_2461_ = 2;
return v___x_2461_;
}
else
{
uint8_t v___x_2462_; 
v___x_2462_ = 0;
return v___x_2462_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_e_2463_){
_start:
{
uint8_t v_res_2464_; lean_object* v_r_2465_; 
v_res_2464_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_e_2463_);
lean_dec_ref(v_e_2463_);
v_r_2465_ = lean_box(v_res_2464_);
return v_r_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t v_sz_2466_, size_t v_i_2467_, lean_object* v_bs_2468_){
_start:
{
uint8_t v___x_2469_; 
v___x_2469_ = lean_usize_dec_lt(v_i_2467_, v_sz_2466_);
if (v___x_2469_ == 0)
{
return v_bs_2468_;
}
else
{
lean_object* v_v_2470_; lean_object* v_msg_2471_; lean_object* v___x_2472_; lean_object* v_bs_x27_2473_; size_t v___x_2474_; size_t v___x_2475_; lean_object* v___x_2476_; 
v_v_2470_ = lean_array_uget_borrowed(v_bs_2468_, v_i_2467_);
v_msg_2471_ = lean_ctor_get(v_v_2470_, 1);
lean_inc_ref(v_msg_2471_);
v___x_2472_ = lean_unsigned_to_nat(0u);
v_bs_x27_2473_ = lean_array_uset(v_bs_2468_, v_i_2467_, v___x_2472_);
v___x_2474_ = ((size_t)1ULL);
v___x_2475_ = lean_usize_add(v_i_2467_, v___x_2474_);
v___x_2476_ = lean_array_uset(v_bs_x27_2473_, v_i_2467_, v_msg_2471_);
v_i_2467_ = v___x_2475_;
v_bs_2468_ = v___x_2476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2478_, lean_object* v_i_2479_, lean_object* v_bs_2480_){
_start:
{
size_t v_sz_boxed_2481_; size_t v_i_boxed_2482_; lean_object* v_res_2483_; 
v_sz_boxed_2481_ = lean_unbox_usize(v_sz_2478_);
lean_dec(v_sz_2478_);
v_i_boxed_2482_ = lean_unbox_usize(v_i_2479_);
lean_dec(v_i_2479_);
v_res_2483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_boxed_2481_, v_i_boxed_2482_, v_bs_2480_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object* v_oldTraces_2484_, lean_object* v_data_2485_, lean_object* v_ref_2486_, lean_object* v_msg_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_fileName_2493_; lean_object* v_fileMap_2494_; lean_object* v_options_2495_; lean_object* v_currRecDepth_2496_; lean_object* v_maxRecDepth_2497_; lean_object* v_ref_2498_; lean_object* v_currNamespace_2499_; lean_object* v_openDecls_2500_; lean_object* v_initHeartbeats_2501_; lean_object* v_maxHeartbeats_2502_; lean_object* v_quotContext_2503_; lean_object* v_currMacroScope_2504_; uint8_t v_diag_2505_; lean_object* v_cancelTk_x3f_2506_; uint8_t v_suppressElabErrors_2507_; lean_object* v_inheritedTraceOptions_2508_; lean_object* v___x_2509_; lean_object* v_traceState_2510_; lean_object* v_traces_2511_; lean_object* v_ref_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; size_t v_sz_2515_; size_t v___x_2516_; lean_object* v___x_2517_; lean_object* v_msg_2518_; lean_object* v___x_2519_; lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2557_; 
v_fileName_2493_ = lean_ctor_get(v___y_2490_, 0);
v_fileMap_2494_ = lean_ctor_get(v___y_2490_, 1);
v_options_2495_ = lean_ctor_get(v___y_2490_, 2);
v_currRecDepth_2496_ = lean_ctor_get(v___y_2490_, 3);
v_maxRecDepth_2497_ = lean_ctor_get(v___y_2490_, 4);
v_ref_2498_ = lean_ctor_get(v___y_2490_, 5);
v_currNamespace_2499_ = lean_ctor_get(v___y_2490_, 6);
v_openDecls_2500_ = lean_ctor_get(v___y_2490_, 7);
v_initHeartbeats_2501_ = lean_ctor_get(v___y_2490_, 8);
v_maxHeartbeats_2502_ = lean_ctor_get(v___y_2490_, 9);
v_quotContext_2503_ = lean_ctor_get(v___y_2490_, 10);
v_currMacroScope_2504_ = lean_ctor_get(v___y_2490_, 11);
v_diag_2505_ = lean_ctor_get_uint8(v___y_2490_, sizeof(void*)*14);
v_cancelTk_x3f_2506_ = lean_ctor_get(v___y_2490_, 12);
v_suppressElabErrors_2507_ = lean_ctor_get_uint8(v___y_2490_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2508_ = lean_ctor_get(v___y_2490_, 13);
v___x_2509_ = lean_st_ref_get(v___y_2491_);
v_traceState_2510_ = lean_ctor_get(v___x_2509_, 4);
lean_inc_ref(v_traceState_2510_);
lean_dec(v___x_2509_);
v_traces_2511_ = lean_ctor_get(v_traceState_2510_, 0);
lean_inc_ref(v_traces_2511_);
lean_dec_ref(v_traceState_2510_);
v_ref_2512_ = l_Lean_replaceRef(v_ref_2486_, v_ref_2498_);
lean_inc_ref(v_inheritedTraceOptions_2508_);
lean_inc(v_cancelTk_x3f_2506_);
lean_inc(v_currMacroScope_2504_);
lean_inc(v_quotContext_2503_);
lean_inc(v_maxHeartbeats_2502_);
lean_inc(v_initHeartbeats_2501_);
lean_inc(v_openDecls_2500_);
lean_inc(v_currNamespace_2499_);
lean_inc(v_maxRecDepth_2497_);
lean_inc(v_currRecDepth_2496_);
lean_inc_ref(v_options_2495_);
lean_inc_ref(v_fileMap_2494_);
lean_inc_ref(v_fileName_2493_);
v___x_2513_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2513_, 0, v_fileName_2493_);
lean_ctor_set(v___x_2513_, 1, v_fileMap_2494_);
lean_ctor_set(v___x_2513_, 2, v_options_2495_);
lean_ctor_set(v___x_2513_, 3, v_currRecDepth_2496_);
lean_ctor_set(v___x_2513_, 4, v_maxRecDepth_2497_);
lean_ctor_set(v___x_2513_, 5, v_ref_2512_);
lean_ctor_set(v___x_2513_, 6, v_currNamespace_2499_);
lean_ctor_set(v___x_2513_, 7, v_openDecls_2500_);
lean_ctor_set(v___x_2513_, 8, v_initHeartbeats_2501_);
lean_ctor_set(v___x_2513_, 9, v_maxHeartbeats_2502_);
lean_ctor_set(v___x_2513_, 10, v_quotContext_2503_);
lean_ctor_set(v___x_2513_, 11, v_currMacroScope_2504_);
lean_ctor_set(v___x_2513_, 12, v_cancelTk_x3f_2506_);
lean_ctor_set(v___x_2513_, 13, v_inheritedTraceOptions_2508_);
lean_ctor_set_uint8(v___x_2513_, sizeof(void*)*14, v_diag_2505_);
lean_ctor_set_uint8(v___x_2513_, sizeof(void*)*14 + 1, v_suppressElabErrors_2507_);
v___x_2514_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2511_);
lean_dec_ref(v_traces_2511_);
v_sz_2515_ = lean_array_size(v___x_2514_);
v___x_2516_ = ((size_t)0ULL);
v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_2515_, v___x_2516_, v___x_2514_);
v_msg_2518_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2518_, 0, v_data_2485_);
lean_ctor_set(v_msg_2518_, 1, v_msg_2487_);
lean_ctor_set(v_msg_2518_, 2, v___x_2517_);
v___x_2519_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2518_, v___y_2488_, v___y_2489_, v___x_2513_, v___y_2491_);
lean_dec_ref_known(v___x_2513_, 14);
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2522_ = v___x_2519_;
v_isShared_2523_ = v_isSharedCheck_2557_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2557_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v_traceState_2525_; lean_object* v_env_2526_; lean_object* v_nextMacroScope_2527_; lean_object* v_ngen_2528_; lean_object* v_auxDeclNGen_2529_; lean_object* v_cache_2530_; lean_object* v_messages_2531_; lean_object* v_infoState_2532_; lean_object* v_snapshotTasks_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2556_; 
v___x_2524_ = lean_st_ref_take(v___y_2491_);
v_traceState_2525_ = lean_ctor_get(v___x_2524_, 4);
v_env_2526_ = lean_ctor_get(v___x_2524_, 0);
v_nextMacroScope_2527_ = lean_ctor_get(v___x_2524_, 1);
v_ngen_2528_ = lean_ctor_get(v___x_2524_, 2);
v_auxDeclNGen_2529_ = lean_ctor_get(v___x_2524_, 3);
v_cache_2530_ = lean_ctor_get(v___x_2524_, 5);
v_messages_2531_ = lean_ctor_get(v___x_2524_, 6);
v_infoState_2532_ = lean_ctor_get(v___x_2524_, 7);
v_snapshotTasks_2533_ = lean_ctor_get(v___x_2524_, 8);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2535_ = v___x_2524_;
v_isShared_2536_ = v_isSharedCheck_2556_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_snapshotTasks_2533_);
lean_inc(v_infoState_2532_);
lean_inc(v_messages_2531_);
lean_inc(v_cache_2530_);
lean_inc(v_traceState_2525_);
lean_inc(v_auxDeclNGen_2529_);
lean_inc(v_ngen_2528_);
lean_inc(v_nextMacroScope_2527_);
lean_inc(v_env_2526_);
lean_dec(v___x_2524_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2556_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
uint64_t v_tid_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2554_; 
v_tid_2537_ = lean_ctor_get_uint64(v_traceState_2525_, sizeof(void*)*1);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_traceState_2525_);
if (v_isSharedCheck_2554_ == 0)
{
lean_object* v_unused_2555_; 
v_unused_2555_ = lean_ctor_get(v_traceState_2525_, 0);
lean_dec(v_unused_2555_);
v___x_2539_ = v_traceState_2525_;
v_isShared_2540_ = v_isSharedCheck_2554_;
goto v_resetjp_2538_;
}
else
{
lean_dec(v_traceState_2525_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2554_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2541_, 0, v_ref_2486_);
lean_ctor_set(v___x_2541_, 1, v_a_2520_);
v___x_2542_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2484_, v___x_2541_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2542_);
v___x_2544_ = v___x_2539_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2542_);
lean_ctor_set_uint64(v_reuseFailAlloc_2553_, sizeof(void*)*1, v_tid_2537_);
v___x_2544_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2546_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 4, v___x_2544_);
v___x_2546_ = v___x_2535_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_env_2526_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_nextMacroScope_2527_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_ngen_2528_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_auxDeclNGen_2529_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v___x_2544_);
lean_ctor_set(v_reuseFailAlloc_2552_, 5, v_cache_2530_);
lean_ctor_set(v_reuseFailAlloc_2552_, 6, v_messages_2531_);
lean_ctor_set(v_reuseFailAlloc_2552_, 7, v_infoState_2532_);
lean_ctor_set(v_reuseFailAlloc_2552_, 8, v_snapshotTasks_2533_);
v___x_2546_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2547_ = lean_st_ref_set(v___y_2491_, v___x_2546_);
v___x_2548_ = lean_box(0);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 0, v___x_2548_);
v___x_2550_ = v___x_2522_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_2558_, lean_object* v_data_2559_, lean_object* v_ref_2560_, lean_object* v_msg_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2558_, v_data_2559_, v_ref_2560_, v_msg_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
return v_res_2567_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_2570_ = l_Lean_stringToMessageData(v___x_2569_);
return v___x_2570_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2571_; double v___x_2572_; 
v___x_2571_ = lean_unsigned_to_nat(1000u);
v___x_2572_ = lean_float_of_nat(v___x_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_2573_, uint8_t v_collapsed_2574_, lean_object* v_tag_2575_, lean_object* v_opts_2576_, uint8_t v_clsEnabled_2577_, lean_object* v_oldTraces_2578_, lean_object* v_msg_2579_, lean_object* v_resStartStop_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_fst_2589_; lean_object* v_snd_2590_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v_data_2594_; lean_object* v_fst_2605_; lean_object* v_snd_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; lean_object* v___y_2610_; lean_object* v_a_2611_; uint8_t v___y_2626_; double v___y_2657_; 
v_fst_2589_ = lean_ctor_get(v_resStartStop_2580_, 0);
lean_inc(v_fst_2589_);
v_snd_2590_ = lean_ctor_get(v_resStartStop_2580_, 1);
lean_inc(v_snd_2590_);
lean_dec_ref(v_resStartStop_2580_);
v_fst_2605_ = lean_ctor_get(v_snd_2590_, 0);
lean_inc(v_fst_2605_);
v_snd_2606_ = lean_ctor_get(v_snd_2590_, 1);
lean_inc(v_snd_2606_);
lean_dec(v_snd_2590_);
v___x_2607_ = l_Lean_trace_profiler;
v___x_2608_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2576_, v___x_2607_);
if (v___x_2608_ == 0)
{
v___y_2626_ = v___x_2608_;
goto v___jp_2625_;
}
else
{
lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2662_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2663_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2576_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2665_; double v___x_2666_; double v___x_2667_; double v___x_2668_; 
v___x_2664_ = l_Lean_trace_profiler_threshold;
v___x_2665_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2576_, v___x_2664_);
v___x_2666_ = lean_float_of_nat(v___x_2665_);
v___x_2667_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_2668_ = lean_float_div(v___x_2666_, v___x_2667_);
v___y_2657_ = v___x_2668_;
goto v___jp_2656_;
}
else
{
lean_object* v___x_2669_; lean_object* v___x_2670_; double v___x_2671_; 
v___x_2669_ = l_Lean_trace_profiler_threshold;
v___x_2670_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2576_, v___x_2669_);
v___x_2671_ = lean_float_of_nat(v___x_2670_);
v___y_2657_ = v___x_2671_;
goto v___jp_2656_;
}
}
v___jp_2591_:
{
lean_object* v___x_2595_; 
lean_inc(v___y_2593_);
v___x_2595_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2578_, v_data_2594_, v___y_2593_, v___y_2592_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v___x_2596_; 
lean_dec_ref_known(v___x_2595_, 1);
v___x_2596_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2589_);
return v___x_2596_;
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v_fst_2589_);
v_a_2597_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2595_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2595_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
v___jp_2609_:
{
uint8_t v_result_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; double v___x_2615_; lean_object* v_data_2616_; 
v_result_2612_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_fst_2589_);
v___x_2613_ = lean_box(v_result_2612_);
v___x_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
v___x_2615_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__0);
lean_inc_ref(v_tag_2575_);
lean_inc_ref(v___x_2614_);
lean_inc(v_cls_2573_);
v_data_2616_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2616_, 0, v_cls_2573_);
lean_ctor_set(v_data_2616_, 1, v___x_2614_);
lean_ctor_set(v_data_2616_, 2, v_tag_2575_);
lean_ctor_set_float(v_data_2616_, sizeof(void*)*3, v___x_2615_);
lean_ctor_set_float(v_data_2616_, sizeof(void*)*3 + 8, v___x_2615_);
lean_ctor_set_uint8(v_data_2616_, sizeof(void*)*3 + 16, v_collapsed_2574_);
if (v___x_2608_ == 0)
{
lean_dec_ref_known(v___x_2614_, 1);
lean_dec(v_snd_2606_);
lean_dec(v_fst_2605_);
lean_dec_ref(v_tag_2575_);
lean_dec(v_cls_2573_);
v___y_2592_ = v_a_2611_;
v___y_2593_ = v___y_2610_;
v_data_2594_ = v_data_2616_;
goto v___jp_2591_;
}
else
{
lean_object* v_data_2617_; double v___x_2618_; double v___x_2619_; 
lean_dec_ref_known(v_data_2616_, 3);
v_data_2617_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2617_, 0, v_cls_2573_);
lean_ctor_set(v_data_2617_, 1, v___x_2614_);
lean_ctor_set(v_data_2617_, 2, v_tag_2575_);
v___x_2618_ = lean_unbox_float(v_fst_2605_);
lean_dec(v_fst_2605_);
lean_ctor_set_float(v_data_2617_, sizeof(void*)*3, v___x_2618_);
v___x_2619_ = lean_unbox_float(v_snd_2606_);
lean_dec(v_snd_2606_);
lean_ctor_set_float(v_data_2617_, sizeof(void*)*3 + 8, v___x_2619_);
lean_ctor_set_uint8(v_data_2617_, sizeof(void*)*3 + 16, v_collapsed_2574_);
v___y_2592_ = v_a_2611_;
v___y_2593_ = v___y_2610_;
v_data_2594_ = v_data_2617_;
goto v___jp_2591_;
}
}
v___jp_2620_:
{
lean_object* v_ref_2621_; lean_object* v___x_2622_; 
v_ref_2621_ = lean_ctor_get(v___y_2586_, 5);
lean_inc(v___y_2587_);
lean_inc_ref(v___y_2586_);
lean_inc(v___y_2585_);
lean_inc_ref(v___y_2584_);
lean_inc(v___y_2583_);
lean_inc_ref(v___y_2582_);
lean_inc(v___y_2581_);
lean_inc(v_fst_2589_);
v___x_2622_ = lean_apply_9(v_msg_2579_, v_fst_2589_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, lean_box(0));
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___x_2622_, 1);
v___y_2610_ = v_ref_2621_;
v_a_2611_ = v_a_2623_;
goto v___jp_2609_;
}
else
{
lean_object* v___x_2624_; 
lean_dec_ref_known(v___x_2622_, 1);
v___x_2624_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_2610_ = v_ref_2621_;
v_a_2611_ = v___x_2624_;
goto v___jp_2609_;
}
}
v___jp_2625_:
{
if (v_clsEnabled_2577_ == 0)
{
if (v___y_2626_ == 0)
{
lean_object* v___x_2627_; lean_object* v_traceState_2628_; lean_object* v_env_2629_; lean_object* v_nextMacroScope_2630_; lean_object* v_ngen_2631_; lean_object* v_auxDeclNGen_2632_; lean_object* v_cache_2633_; lean_object* v_messages_2634_; lean_object* v_infoState_2635_; lean_object* v_snapshotTasks_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2655_; 
lean_dec(v_snd_2606_);
lean_dec(v_fst_2605_);
lean_dec_ref(v_msg_2579_);
lean_dec_ref(v_tag_2575_);
lean_dec(v_cls_2573_);
v___x_2627_ = lean_st_ref_take(v___y_2587_);
v_traceState_2628_ = lean_ctor_get(v___x_2627_, 4);
v_env_2629_ = lean_ctor_get(v___x_2627_, 0);
v_nextMacroScope_2630_ = lean_ctor_get(v___x_2627_, 1);
v_ngen_2631_ = lean_ctor_get(v___x_2627_, 2);
v_auxDeclNGen_2632_ = lean_ctor_get(v___x_2627_, 3);
v_cache_2633_ = lean_ctor_get(v___x_2627_, 5);
v_messages_2634_ = lean_ctor_get(v___x_2627_, 6);
v_infoState_2635_ = lean_ctor_get(v___x_2627_, 7);
v_snapshotTasks_2636_ = lean_ctor_get(v___x_2627_, 8);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2638_ = v___x_2627_;
v_isShared_2639_ = v_isSharedCheck_2655_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_snapshotTasks_2636_);
lean_inc(v_infoState_2635_);
lean_inc(v_messages_2634_);
lean_inc(v_cache_2633_);
lean_inc(v_traceState_2628_);
lean_inc(v_auxDeclNGen_2632_);
lean_inc(v_ngen_2631_);
lean_inc(v_nextMacroScope_2630_);
lean_inc(v_env_2629_);
lean_dec(v___x_2627_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2655_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
uint64_t v_tid_2640_; lean_object* v_traces_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2654_; 
v_tid_2640_ = lean_ctor_get_uint64(v_traceState_2628_, sizeof(void*)*1);
v_traces_2641_ = lean_ctor_get(v_traceState_2628_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_traceState_2628_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2643_ = v_traceState_2628_;
v_isShared_2644_ = v_isSharedCheck_2654_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_traces_2641_);
lean_dec(v_traceState_2628_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2654_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2645_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2578_, v_traces_2641_);
lean_dec_ref(v_traces_2641_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2645_);
v___x_2647_ = v___x_2643_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2645_);
lean_ctor_set_uint64(v_reuseFailAlloc_2653_, sizeof(void*)*1, v_tid_2640_);
v___x_2647_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2649_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 4, v___x_2647_);
v___x_2649_ = v___x_2638_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_env_2629_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_nextMacroScope_2630_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v_ngen_2631_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v_auxDeclNGen_2632_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2652_, 5, v_cache_2633_);
lean_ctor_set(v_reuseFailAlloc_2652_, 6, v_messages_2634_);
lean_ctor_set(v_reuseFailAlloc_2652_, 7, v_infoState_2635_);
lean_ctor_set(v_reuseFailAlloc_2652_, 8, v_snapshotTasks_2636_);
v___x_2649_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_st_ref_set(v___y_2587_, v___x_2649_);
v___x_2651_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2589_);
return v___x_2651_;
}
}
}
}
}
else
{
goto v___jp_2620_;
}
}
else
{
goto v___jp_2620_;
}
}
v___jp_2656_:
{
double v___x_2658_; double v___x_2659_; double v___x_2660_; uint8_t v___x_2661_; 
v___x_2658_ = lean_unbox_float(v_snd_2606_);
v___x_2659_ = lean_unbox_float(v_fst_2605_);
v___x_2660_ = lean_float_sub(v___x_2658_, v___x_2659_);
v___x_2661_ = lean_float_decLt(v___y_2657_, v___x_2660_);
v___y_2626_ = v___x_2661_;
goto v___jp_2625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object* v_cls_2672_, lean_object* v_collapsed_2673_, lean_object* v_tag_2674_, lean_object* v_opts_2675_, lean_object* v_clsEnabled_2676_, lean_object* v_oldTraces_2677_, lean_object* v_msg_2678_, lean_object* v_resStartStop_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v_collapsed_boxed_2688_; uint8_t v_clsEnabled_boxed_2689_; lean_object* v_res_2690_; 
v_collapsed_boxed_2688_ = lean_unbox(v_collapsed_2673_);
v_clsEnabled_boxed_2689_ = lean_unbox(v_clsEnabled_2676_);
v_res_2690_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2672_, v_collapsed_boxed_2688_, v_tag_2674_, v_opts_2675_, v_clsEnabled_boxed_2689_, v_oldTraces_2677_, v_msg_2678_, v_resStartStop_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v_opts_2675_);
return v_res_2690_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1));
v___x_2695_ = l_Lean_stringToMessageData(v___x_2694_);
return v___x_2695_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4(void){
_start:
{
lean_object* v___x_2697_; double v___x_2698_; 
v___x_2697_ = lean_unsigned_to_nat(1000000000u);
v___x_2698_ = lean_float_of_nat(v___x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object* v_P_2699_, lean_object* v_lhs_2700_, lean_object* v_rhs_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v_options_2730_; lean_object* v_inheritedTraceOptions_2731_; uint8_t v_hasTrace_2732_; lean_object* v_cls_2733_; lean_object* v___f_2734_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; uint8_t v_____do__lift_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; uint8_t v___x_2855_; 
v_options_2730_ = lean_ctor_get(v_a_2707_, 2);
v_inheritedTraceOptions_2731_ = lean_ctor_get(v_a_2707_, 13);
v_hasTrace_2732_ = lean_ctor_get_uint8(v_options_2730_, sizeof(void*)*1);
v_cls_2733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_2734_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_2855_ = lean_bool_not(v_hasTrace_2732_);
if (v___x_2855_ == 0)
{
lean_object* v___f_2856_; lean_object* v___x_2857_; lean_object* v___y_2859_; uint8_t v___y_2860_; lean_object* v___y_2861_; lean_object* v_a_2862_; lean_object* v___y_2872_; uint8_t v___y_2873_; lean_object* v___y_2874_; lean_object* v_a_2875_; lean_object* v___y_2878_; uint8_t v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2892_; uint8_t v___y_2893_; lean_object* v___y_2894_; lean_object* v_a_2895_; lean_object* v___y_2908_; uint8_t v___y_2909_; lean_object* v___y_2910_; lean_object* v_a_2911_; lean_object* v___y_2914_; uint8_t v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; uint8_t v___y_2928_; uint8_t v_a_2962_; 
v___f_2856_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3));
v___x_2857_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___closed__1));
if (v_hasTrace_2732_ == 0)
{
v_a_2962_ = v_hasTrace_2732_;
goto v___jp_2961_;
}
else
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_2969_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2731_, v_options_2730_, v___x_2968_);
if (v___x_2969_ == 0)
{
v_a_2962_ = v___x_2969_;
goto v___jp_2961_;
}
else
{
v___y_2928_ = v___x_2969_;
goto v___jp_2927_;
}
}
v___jp_2858_:
{
lean_object* v___x_2863_; double v___x_2864_; double v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2863_ = lean_io_get_num_heartbeats();
v___x_2864_ = lean_float_of_nat(v___y_2861_);
v___x_2865_ = lean_float_of_nat(v___x_2863_);
v___x_2866_ = lean_box_float(v___x_2864_);
v___x_2867_ = lean_box_float(v___x_2865_);
v___x_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2869_, 0, v_a_2862_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2733_, v___x_2855_, v___x_2857_, v_options_2730_, v___y_2860_, v___y_2859_, v___f_2856_, v___x_2869_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
return v___x_2870_;
}
v___jp_2871_:
{
lean_object* v___x_2876_; 
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v_a_2875_);
v___y_2859_ = v___y_2872_;
v___y_2860_ = v___y_2873_;
v___y_2861_ = v___y_2874_;
v_a_2862_ = v___x_2876_;
goto v___jp_2858_;
}
v___jp_2877_:
{
if (lean_obj_tag(v___y_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
v_a_2882_ = lean_ctor_get(v___y_2881_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___y_2881_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___y_2881_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___y_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
lean_ctor_set_tag(v___x_2884_, 1);
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
v___y_2859_ = v___y_2878_;
v___y_2860_ = v___y_2879_;
v___y_2861_ = v___y_2880_;
v_a_2862_ = v___x_2887_;
goto v___jp_2858_;
}
}
}
else
{
lean_object* v_a_2890_; 
v_a_2890_ = lean_ctor_get(v___y_2881_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___y_2881_, 1);
v___y_2872_ = v___y_2878_;
v___y_2873_ = v___y_2879_;
v___y_2874_ = v___y_2880_;
v_a_2875_ = v_a_2890_;
goto v___jp_2871_;
}
}
v___jp_2891_:
{
lean_object* v___x_2896_; double v___x_2897_; double v___x_2898_; double v___x_2899_; double v___x_2900_; double v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2896_ = lean_io_mono_nanos_now();
v___x_2897_ = lean_float_of_nat(v___y_2894_);
v___x_2898_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4);
v___x_2899_ = lean_float_div(v___x_2897_, v___x_2898_);
v___x_2900_ = lean_float_of_nat(v___x_2896_);
v___x_2901_ = lean_float_div(v___x_2900_, v___x_2898_);
v___x_2902_ = lean_box_float(v___x_2899_);
v___x_2903_ = lean_box_float(v___x_2901_);
v___x_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2902_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2905_, 0, v_a_2895_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2733_, v___x_2855_, v___x_2857_, v_options_2730_, v___y_2893_, v___y_2892_, v___f_2856_, v___x_2905_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
return v___x_2906_;
}
v___jp_2907_:
{
lean_object* v___x_2912_; 
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_a_2911_);
v___y_2892_ = v___y_2908_;
v___y_2893_ = v___y_2909_;
v___y_2894_ = v___y_2910_;
v_a_2895_ = v___x_2912_;
goto v___jp_2891_;
}
v___jp_2913_:
{
if (lean_obj_tag(v___y_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
v_a_2918_ = lean_ctor_get(v___y_2917_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___y_2917_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___y_2917_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___y_2917_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
lean_ctor_set_tag(v___x_2920_, 1);
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
v___y_2892_ = v___y_2914_;
v___y_2893_ = v___y_2915_;
v___y_2894_ = v___y_2916_;
v_a_2895_ = v___x_2923_;
goto v___jp_2891_;
}
}
}
else
{
lean_object* v_a_2926_; 
v_a_2926_ = lean_ctor_get(v___y_2917_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___y_2917_, 1);
v___y_2908_ = v___y_2914_;
v___y_2909_ = v___y_2915_;
v___y_2910_ = v___y_2916_;
v_a_2911_ = v_a_2926_;
goto v___jp_2907_;
}
}
v___jp_2927_:
{
lean_object* v___x_2929_; lean_object* v_a_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; 
v___x_2929_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_2708_);
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref(v___x_2929_);
v___x_2931_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2932_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_2730_, v___x_2931_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v_a_2935_; uint8_t v___x_2936_; 
v___x_2933_ = lean_io_mono_nanos_now();
v___x_2934_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2733_, v_inheritedTraceOptions_2731_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref(v___x_2934_);
v___x_2936_ = lean_unbox(v_a_2935_);
lean_dec(v_a_2935_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = lean_box(0);
v___x_2938_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2700_, v_rhs_2701_, v_P_2699_, v_cls_2733_, v___f_2734_, v___x_2937_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
v___y_2914_ = v_a_2930_;
v___y_2915_ = v___y_2928_;
v___y_2916_ = v___x_2933_;
v___y_2917_ = v___x_2938_;
goto v___jp_2913_;
}
else
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2939_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2701_);
lean_inc_ref(v_lhs_2700_);
lean_inc_ref(v_P_2699_);
v___x_2940_ = l_Lean_mkAppB(v_P_2699_, v_lhs_2700_, v_rhs_2701_);
v___x_2941_ = l_Lean_indentExpr(v___x_2940_);
v___x_2942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2939_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2733_, v___x_2942_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2945_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2700_, v_rhs_2701_, v_P_2699_, v_cls_2733_, v___f_2734_, v_a_2944_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
v___y_2914_ = v_a_2930_;
v___y_2915_ = v___y_2928_;
v___y_2916_ = v___x_2933_;
v___y_2917_ = v___x_2945_;
goto v___jp_2913_;
}
else
{
lean_object* v_a_2946_; 
lean_dec_ref(v_rhs_2701_);
lean_dec_ref(v_lhs_2700_);
lean_dec_ref(v_P_2699_);
v_a_2946_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2943_, 1);
v___y_2908_ = v_a_2930_;
v___y_2909_ = v___y_2928_;
v___y_2910_ = v___x_2933_;
v_a_2911_ = v_a_2946_;
goto v___jp_2907_;
}
}
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v_a_2949_; uint8_t v___x_2950_; 
v___x_2947_ = lean_io_get_num_heartbeats();
v___x_2948_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2733_, v_inheritedTraceOptions_2731_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref(v___x_2948_);
v___x_2950_ = lean_unbox(v_a_2949_);
lean_dec(v_a_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = lean_box(0);
v___x_2952_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(v_lhs_2700_, v_rhs_2701_, v_P_2699_, v___x_2932_, v_cls_2733_, v___f_2734_, v___x_2951_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
v___y_2878_ = v_a_2930_;
v___y_2879_ = v___y_2928_;
v___y_2880_ = v___x_2947_;
v___y_2881_ = v___x_2952_;
goto v___jp_2877_;
}
else
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2953_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2701_);
lean_inc_ref(v_lhs_2700_);
lean_inc_ref(v_P_2699_);
v___x_2954_ = l_Lean_mkAppB(v_P_2699_, v_lhs_2700_, v_rhs_2701_);
v___x_2955_ = l_Lean_indentExpr(v___x_2954_);
v___x_2956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2953_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___x_2957_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2733_, v___x_2956_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref_known(v___x_2957_, 1);
v___x_2959_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(v_lhs_2700_, v_rhs_2701_, v_P_2699_, v___x_2932_, v_cls_2733_, v___f_2734_, v_a_2958_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
v___y_2878_ = v_a_2930_;
v___y_2879_ = v___y_2928_;
v___y_2880_ = v___x_2947_;
v___y_2881_ = v___x_2959_;
goto v___jp_2877_;
}
else
{
lean_object* v_a_2960_; 
lean_dec_ref(v_rhs_2701_);
lean_dec_ref(v_lhs_2700_);
lean_dec_ref(v_P_2699_);
v_a_2960_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2957_, 1);
v___y_2872_ = v_a_2930_;
v___y_2873_ = v___y_2928_;
v___y_2874_ = v___x_2947_;
v_a_2875_ = v_a_2960_;
goto v___jp_2871_;
}
}
}
}
v___jp_2961_:
{
lean_object* v___x_2963_; uint8_t v___x_2964_; 
v___x_2963_ = l_Lean_trace_profiler;
v___x_2964_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_2730_, v___x_2963_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; lean_object* v_a_2966_; uint8_t v___x_2967_; 
v___x_2965_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2733_, v_inheritedTraceOptions_2731_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref(v___x_2965_);
v___x_2967_ = lean_unbox(v_a_2966_);
lean_dec(v_a_2966_);
v_____do__lift_2834_ = v___x_2967_;
v___y_2835_ = v_a_2702_;
v___y_2836_ = v_a_2703_;
v___y_2837_ = v_a_2704_;
v___y_2838_ = v_a_2705_;
v___y_2839_ = v_a_2706_;
v___y_2840_ = v_a_2707_;
v___y_2841_ = v_a_2708_;
goto v___jp_2833_;
}
else
{
v___y_2928_ = v_a_2962_;
goto v___jp_2927_;
}
}
}
else
{
lean_object* v___x_2970_; lean_object* v_a_2971_; uint8_t v___x_2972_; 
v___x_2970_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2733_, v_inheritedTraceOptions_2731_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref(v___x_2970_);
v___x_2972_ = lean_unbox(v_a_2971_);
lean_dec(v_a_2971_);
v_____do__lift_2834_ = v___x_2972_;
v___y_2835_ = v_a_2702_;
v___y_2836_ = v_a_2703_;
v___y_2837_ = v_a_2704_;
v___y_2838_ = v_a_2705_;
v___y_2839_ = v_a_2706_;
v___y_2840_ = v_a_2707_;
v___y_2841_ = v_a_2708_;
goto v___jp_2833_;
}
v___jp_2710_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2717_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2);
v___x_2718_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3));
v___x_2719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2719_, 0, v___y_2712_);
lean_ctor_set(v___x_2719_, 1, v___x_2717_);
lean_ctor_set(v___x_2719_, 2, v___x_2718_);
v___x_2720_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2711_, v___x_2719_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
return v___x_2720_;
}
v___jp_2721_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
return v___x_2723_;
}
v___jp_2724_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
v___jp_2727_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
return v___x_2729_;
}
v___jp_2735_:
{
lean_object* v___x_2743_; 
lean_inc_ref(v_lhs_2700_);
v___x_2743_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2700_);
if (lean_obj_tag(v___x_2743_) == 1)
{
lean_object* v_val_2744_; lean_object* v___x_2745_; 
v_val_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_val_2744_);
lean_dec_ref_known(v___x_2743_, 1);
lean_inc_ref(v_rhs_2701_);
v___x_2745_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2701_);
if (lean_obj_tag(v___x_2745_) == 1)
{
lean_object* v_val_2746_; uint8_t v___x_2747_; uint8_t v___x_2748_; 
v_val_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_val_2746_);
lean_dec_ref_known(v___x_2745_, 1);
v___x_2747_ = lean_expr_eqv(v_val_2744_, v_val_2746_);
v___x_2748_ = lean_bool_not(v___x_2747_);
if (v___x_2748_ == 0)
{
lean_object* v_options_2749_; lean_object* v_inheritedTraceOptions_2750_; uint8_t v_hasTrace_2751_; uint8_t v___x_2752_; lean_object* v___x_2753_; lean_object* v___f_2754_; 
lean_dec(v_val_2746_);
v_options_2749_ = lean_ctor_get(v___y_2741_, 2);
v_inheritedTraceOptions_2750_ = lean_ctor_get(v___y_2741_, 13);
v_hasTrace_2751_ = lean_ctor_get_uint8(v_options_2749_, sizeof(void*)*1);
v___x_2752_ = 1;
v___x_2753_ = lean_box(v___x_2752_);
lean_inc(v_val_2744_);
v___f_2754_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 11, 5);
lean_closure_set(v___f_2754_, 0, v_val_2744_);
lean_closure_set(v___f_2754_, 1, v_lhs_2700_);
lean_closure_set(v___f_2754_, 2, v_rhs_2701_);
lean_closure_set(v___f_2754_, 3, v_P_2699_);
lean_closure_set(v___f_2754_, 4, v___x_2753_);
if (v_hasTrace_2751_ == 0)
{
v___y_2711_ = v___f_2754_;
v___y_2712_ = v_val_2744_;
v___y_2713_ = v___y_2739_;
v___y_2714_ = v___y_2740_;
v___y_2715_ = v___y_2741_;
v___y_2716_ = v___y_2742_;
goto v___jp_2710_;
}
else
{
lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_2756_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2750_, v_options_2749_, v___x_2755_);
if (v___x_2756_ == 0)
{
v___y_2711_ = v___f_2754_;
v___y_2712_ = v_val_2744_;
v___y_2713_ = v___y_2739_;
v___y_2714_ = v___y_2740_;
v___y_2715_ = v___y_2741_;
v___y_2716_ = v___y_2742_;
goto v___jp_2710_;
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2757_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
lean_inc(v_val_2744_);
v___x_2758_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2744_);
v___x_2759_ = l_Lean_MessageData_ofExpr(v___x_2758_);
v___x_2760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2757_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2733_, v___x_2762_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_dec_ref_known(v___x_2763_, 1);
v___y_2711_ = v___f_2754_;
v___y_2712_ = v_val_2744_;
v___y_2713_ = v___y_2739_;
v___y_2714_ = v___y_2740_;
v___y_2715_ = v___y_2741_;
v___y_2716_ = v___y_2742_;
goto v___jp_2710_;
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec_ref(v___f_2754_);
lean_dec(v_val_2744_);
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2772_; lean_object* v___x_2773_; lean_object* v_a_2774_; uint8_t v___x_2775_; 
lean_dec_ref(v_P_2699_);
v_inheritedTraceOptions_2772_ = lean_ctor_get(v___y_2741_, 13);
v___x_2773_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2733_, v_inheritedTraceOptions_2772_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref(v___x_2773_);
v___x_2775_ = lean_unbox(v_a_2774_);
lean_dec(v_a_2774_);
if (v___x_2775_ == 0)
{
lean_dec(v_val_2746_);
lean_dec(v_val_2744_);
lean_dec_ref(v_rhs_2701_);
lean_dec_ref(v_lhs_2700_);
goto v___jp_2727_;
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2776_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9);
v___x_2777_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2744_);
v___x_2778_ = l_Lean_MessageData_ofExpr(v___x_2777_);
v___x_2779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2776_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11);
v___x_2781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2779_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = l_Lean_indentExpr(v_lhs_2700_);
v___x_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2781_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13);
v___x_2785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2783_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2746_);
v___x_2787_ = l_Lean_MessageData_ofExpr(v___x_2786_);
v___x_2788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2785_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
v___x_2789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v___x_2780_);
v___x_2790_ = l_Lean_indentExpr(v_rhs_2701_);
v___x_2791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2733_, v___x_2791_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_dec_ref_known(v___x_2792_, 1);
goto v___jp_2727_;
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2792_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2792_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2801_; lean_object* v___x_2802_; lean_object* v_a_2803_; uint8_t v___x_2804_; 
lean_dec(v___x_2745_);
lean_dec(v_val_2744_);
lean_dec_ref(v_lhs_2700_);
lean_dec_ref(v_P_2699_);
v_inheritedTraceOptions_2801_ = lean_ctor_get(v___y_2741_, 13);
v___x_2802_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2733_, v_inheritedTraceOptions_2801_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref(v___x_2802_);
v___x_2804_ = lean_unbox(v_a_2803_);
lean_dec(v_a_2803_);
if (v___x_2804_ == 0)
{
lean_dec_ref(v_rhs_2701_);
goto v___jp_2724_;
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2805_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2806_ = l_Lean_indentExpr(v_rhs_2701_);
v___x_2807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2805_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2733_, v___x_2807_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_dec_ref_known(v___x_2808_, 1);
goto v___jp_2724_;
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2808_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2808_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2817_; lean_object* v___x_2818_; lean_object* v_a_2819_; uint8_t v___x_2820_; 
lean_dec(v___x_2743_);
lean_dec_ref(v_rhs_2701_);
lean_dec_ref(v_P_2699_);
v_inheritedTraceOptions_2817_ = lean_ctor_get(v___y_2741_, 13);
v___x_2818_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2733_, v_inheritedTraceOptions_2817_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref(v___x_2818_);
v___x_2820_ = lean_unbox(v_a_2819_);
lean_dec(v_a_2819_);
if (v___x_2820_ == 0)
{
lean_dec_ref(v_lhs_2700_);
goto v___jp_2721_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2821_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2822_ = l_Lean_indentExpr(v_lhs_2700_);
v___x_2823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2821_);
lean_ctor_set(v___x_2823_, 1, v___x_2822_);
v___x_2824_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2733_, v___x_2823_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_dec_ref_known(v___x_2824_, 1);
goto v___jp_2721_;
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2824_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2824_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
}
v___jp_2833_:
{
if (v_____do__lift_2834_ == 0)
{
v___y_2736_ = v___y_2835_;
v___y_2737_ = v___y_2836_;
v___y_2738_ = v___y_2837_;
v___y_2739_ = v___y_2838_;
v___y_2740_ = v___y_2839_;
v___y_2741_ = v___y_2840_;
v___y_2742_ = v___y_2841_;
goto v___jp_2735_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2842_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2701_);
lean_inc_ref(v_lhs_2700_);
lean_inc_ref(v_P_2699_);
v___x_2843_ = l_Lean_mkAppB(v_P_2699_, v_lhs_2700_, v_rhs_2701_);
v___x_2844_ = l_Lean_indentExpr(v___x_2843_);
v___x_2845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2842_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
v___x_2846_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2733_, v___x_2845_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_dec_ref_known(v___x_2846_, 1);
v___y_2736_ = v___y_2835_;
v___y_2737_ = v___y_2836_;
v___y_2738_ = v___y_2837_;
v___y_2739_ = v___y_2838_;
v___y_2740_ = v___y_2839_;
v___y_2741_ = v___y_2840_;
v___y_2742_ = v___y_2841_;
goto v___jp_2735_;
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec_ref(v_rhs_2701_);
lean_dec_ref(v_lhs_2700_);
lean_dec_ref(v_P_2699_);
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_2973_, lean_object* v_lhs_2974_, lean_object* v_rhs_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v_P_2973_, v_lhs_2974_, v_rhs_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_a_2976_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_2985_, lean_object* v_msg_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2985_, v_msg_2986_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_2996_, lean_object* v_msg_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(v_cls_2996_, v_msg_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_00_u03b1_3007_, lean_object* v_x_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_3008_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3018_, lean_object* v_x_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_00_u03b1_3018_, v_x_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_oldTraces_3029_, lean_object* v_data_3030_, lean_object* v_ref_3031_, lean_object* v_msg_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3029_, v_data_3030_, v_ref_3031_, v_msg_3032_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_oldTraces_3042_, lean_object* v_data_3043_, lean_object* v_ref_3044_, lean_object* v_msg_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_oldTraces_3042_, v_data_3043_, v_ref_3044_, v_msg_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
return v_res_3054_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5));
v___x_3065_ = l_Lean_stringToMessageData(v___x_3064_);
return v___x_3065_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = l_Lean_checkEmoji;
v___x_3067_ = l_Lean_stringToMessageData(v___x_3066_);
return v___x_3067_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7);
v___x_3069_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6);
v___x_3070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
lean_ctor_set(v___x_3070_, 1, v___x_3068_);
return v___x_3070_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9));
v___x_3073_ = l_Lean_stringToMessageData(v___x_3072_);
return v___x_3073_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10);
v___x_3075_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v___x_3074_);
return v___x_3076_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__13(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__12));
v___x_3079_ = l_Lean_stringToMessageData(v___x_3078_);
return v___x_3079_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__14(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__13);
v___x_3081_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3080_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object* v_e_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3083_, v_a_3088_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3199_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3095_ = v___x_3092_;
v_isShared_3096_ = v_isSharedCheck_3199_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3092_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3199_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3102_ = l_Lean_Expr_cleanupAnnotations(v_a_3093_);
v___x_3103_ = l_Lean_Expr_isApp(v___x_3102_);
if (v___x_3103_ == 0)
{
lean_dec_ref(v___x_3102_);
goto v___jp_3097_;
}
else
{
lean_object* v_arg_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v_arg_3104_ = lean_ctor_get(v___x_3102_, 1);
lean_inc_ref(v_arg_3104_);
v___x_3105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3102_);
v___x_3106_ = l_Lean_Expr_isApp(v___x_3105_);
if (v___x_3106_ == 0)
{
lean_dec_ref(v___x_3105_);
lean_dec_ref(v_arg_3104_);
goto v___jp_3097_;
}
else
{
lean_object* v_arg_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
v_arg_3107_ = lean_ctor_get(v___x_3105_, 1);
lean_inc_ref(v_arg_3107_);
v___x_3108_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3105_);
v___x_3109_ = l_Lean_Expr_isApp(v___x_3108_);
if (v___x_3109_ == 0)
{
lean_dec_ref(v___x_3108_);
lean_dec_ref(v_arg_3107_);
lean_dec_ref(v_arg_3104_);
goto v___jp_3097_;
}
else
{
lean_object* v_arg_3110_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
v_arg_3110_ = lean_ctor_get(v___x_3108_, 1);
lean_inc_ref(v_arg_3110_);
v___x_3135_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3108_);
v___x_3136_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1));
v___x_3137_ = l_Lean_Expr_isConstOf(v___x_3135_, v___x_3136_);
if (v___x_3137_ == 0)
{
uint8_t v___x_3138_; 
v___x_3138_ = l_Lean_Expr_isApp(v___x_3135_);
if (v___x_3138_ == 0)
{
lean_dec_ref(v___x_3135_);
lean_dec_ref(v_arg_3110_);
lean_dec_ref(v_arg_3107_);
lean_dec_ref(v_arg_3104_);
goto v___jp_3097_;
}
else
{
lean_object* v_arg_3139_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___x_3164_; lean_object* v___x_3165_; uint8_t v___x_3166_; 
v_arg_3139_ = lean_ctor_get(v___x_3135_, 1);
lean_inc_ref(v_arg_3139_);
v___x_3164_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3135_);
v___x_3165_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4));
v___x_3166_ = l_Lean_Expr_isConstOf(v___x_3164_, v___x_3165_);
lean_dec_ref(v___x_3164_);
if (v___x_3166_ == 0)
{
lean_dec_ref(v_arg_3139_);
lean_dec_ref(v_arg_3110_);
lean_dec_ref(v_arg_3107_);
lean_dec_ref(v_arg_3104_);
goto v___jp_3097_;
}
else
{
lean_object* v_options_3167_; uint8_t v_hasTrace_3168_; 
lean_del_object(v___x_3095_);
v_options_3167_ = lean_ctor_get(v_a_3089_, 2);
v_hasTrace_3168_ = lean_ctor_get_uint8(v_options_3167_, sizeof(void*)*1);
if (v_hasTrace_3168_ == 0)
{
v___y_3141_ = v_a_3084_;
v___y_3142_ = v_a_3085_;
v___y_3143_ = v_a_3086_;
v___y_3144_ = v_a_3087_;
v___y_3145_ = v_a_3088_;
v___y_3146_ = v_a_3089_;
v___y_3147_ = v_a_3090_;
goto v___jp_3140_;
}
else
{
lean_object* v_inheritedTraceOptions_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v_inheritedTraceOptions_3169_ = lean_ctor_get(v_a_3089_, 13);
v___x_3170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3172_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3169_, v_options_3167_, v___x_3171_);
if (v___x_3172_ == 0)
{
v___y_3141_ = v_a_3084_;
v___y_3142_ = v_a_3085_;
v___y_3143_ = v_a_3086_;
v___y_3144_ = v_a_3087_;
v___y_3145_ = v_a_3088_;
v___y_3146_ = v_a_3089_;
v___y_3147_ = v_a_3090_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11);
v___x_3174_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3170_, v___x_3173_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_dec_ref_known(v___x_3174_, 1);
v___y_3141_ = v_a_3084_;
v___y_3142_ = v_a_3085_;
v___y_3143_ = v_a_3086_;
v___y_3144_ = v_a_3087_;
v___y_3145_ = v_a_3088_;
v___y_3146_ = v_a_3089_;
v___y_3147_ = v_a_3090_;
goto v___jp_3140_;
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec_ref(v_arg_3139_);
lean_dec_ref(v_arg_3110_);
lean_dec_ref(v_arg_3107_);
lean_dec_ref(v_arg_3104_);
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3174_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3174_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
}
}
v___jp_3140_:
{
lean_object* v___x_3148_; 
lean_inc_ref(v_arg_3139_);
v___x_3148_ = l_Lean_Meta_getDecLevel(v_arg_3139_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
lean_dec_ref_known(v___x_3148_, 1);
v___x_3150_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4));
v___x_3151_ = lean_box(0);
v___x_3152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3152_, 0, v_a_3149_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = l_Lean_Expr_const___override(v___x_3150_, v___x_3152_);
v___x_3154_ = l_Lean_mkAppB(v___x_3153_, v_arg_3139_, v_arg_3110_);
v___x_3155_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3154_, v_arg_3107_, v_arg_3104_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
return v___x_3155_;
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref(v_arg_3139_);
lean_dec_ref(v_arg_3110_);
lean_dec_ref(v_arg_3107_);
lean_dec_ref(v_arg_3104_);
v_a_3156_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3148_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3148_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
}
}
else
{
lean_object* v_options_3183_; uint8_t v_hasTrace_3184_; 
lean_dec_ref(v___x_3135_);
lean_del_object(v___x_3095_);
v_options_3183_ = lean_ctor_get(v_a_3089_, 2);
v_hasTrace_3184_ = lean_ctor_get_uint8(v_options_3183_, sizeof(void*)*1);
if (v_hasTrace_3184_ == 0)
{
v___y_3112_ = v_a_3084_;
v___y_3113_ = v_a_3085_;
v___y_3114_ = v_a_3086_;
v___y_3115_ = v_a_3087_;
v___y_3116_ = v_a_3088_;
v___y_3117_ = v_a_3089_;
v___y_3118_ = v_a_3090_;
goto v___jp_3111_;
}
else
{
lean_object* v_inheritedTraceOptions_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; uint8_t v___x_3188_; 
v_inheritedTraceOptions_3185_ = lean_ctor_get(v_a_3089_, 13);
v___x_3186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3188_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3185_, v_options_3183_, v___x_3187_);
if (v___x_3188_ == 0)
{
v___y_3112_ = v_a_3084_;
v___y_3113_ = v_a_3085_;
v___y_3114_ = v_a_3086_;
v___y_3115_ = v_a_3087_;
v___y_3116_ = v_a_3088_;
v___y_3117_ = v_a_3089_;
v___y_3118_ = v_a_3090_;
goto v___jp_3111_;
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__14);
v___x_3190_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3186_, v___x_3189_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_dec_ref_known(v___x_3190_, 1);
v___y_3112_ = v_a_3084_;
v___y_3113_ = v_a_3085_;
v___y_3114_ = v_a_3086_;
v___y_3115_ = v_a_3087_;
v___y_3116_ = v_a_3088_;
v___y_3117_ = v_a_3089_;
v___y_3118_ = v_a_3090_;
goto v___jp_3111_;
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec_ref(v_arg_3110_);
lean_dec_ref(v_arg_3107_);
lean_dec_ref(v_arg_3104_);
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
}
v___jp_3111_:
{
lean_object* v___x_3119_; 
lean_inc_ref(v_arg_3110_);
v___x_3119_ = l_Lean_Meta_getLevel(v_arg_3110_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v___x_3121_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1));
v___x_3122_ = lean_box(0);
v___x_3123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3123_, 0, v_a_3120_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_Expr_const___override(v___x_3121_, v___x_3123_);
v___x_3125_ = l_Lean_Expr_app___override(v___x_3124_, v_arg_3110_);
v___x_3126_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3125_, v_arg_3107_, v_arg_3104_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
return v___x_3126_;
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec_ref(v_arg_3110_);
lean_dec_ref(v_arg_3107_);
lean_dec_ref(v_arg_3104_);
v_a_3127_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3119_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3119_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
}
}
v___jp_3097_:
{
lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3098_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v___x_3098_);
v___x_3100_ = v___x_3095_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
v_a_3200_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3092_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3092_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object* v_e_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(v_e_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
lean_dec(v_a_3215_);
lean_dec_ref(v_a_3214_);
lean_dec(v_a_3213_);
lean_dec_ref(v_a_3212_);
lean_dec(v_a_3211_);
lean_dec_ref(v_a_3210_);
lean_dec(v_a_3209_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__0(lean_object* v_x_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__0___boxed(lean_object* v_x_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__0(v_x_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v_x_3229_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1(lean_object* v_x_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1___closed__0));
v___x_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1___boxed(lean_object* v_x_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__1(v_x_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v_x_3252_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__2(lean_object* v_e_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_e_3262_);
v___x_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__2___boxed(lean_object* v_e_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__2(v_e_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__3(lean_object* v_x_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = lean_box(0);
v___x_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__3___boxed(lean_object* v_x_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___lam__3(v_x_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v_x_3294_);
return v_res_3303_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__5(void){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3310_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__5);
v___x_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
return v___x_3312_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__7(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3313_ = lean_unsigned_to_nat(0u);
v___x_3314_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6);
v___x_3315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
lean_ctor_set(v___x_3315_, 1, v___x_3313_);
return v___x_3315_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__8(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_unsigned_to_nat(32u);
v___x_3317_ = lean_mk_empty_array_with_capacity(v___x_3316_);
v___x_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
return v___x_3318_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__9(void){
_start:
{
size_t v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3319_ = ((size_t)5ULL);
v___x_3320_ = lean_unsigned_to_nat(0u);
v___x_3321_ = lean_unsigned_to_nat(32u);
v___x_3322_ = lean_mk_empty_array_with_capacity(v___x_3321_);
v___x_3323_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__8);
v___x_3324_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v___x_3322_);
lean_ctor_set(v___x_3324_, 2, v___x_3320_);
lean_ctor_set(v___x_3324_, 3, v___x_3320_);
lean_ctor_set_usize(v___x_3324_, 4, v___x_3319_);
return v___x_3324_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__10(void){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3325_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__9);
v___x_3326_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__6);
v___x_3327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
lean_ctor_set(v___x_3327_, 2, v___x_3326_);
lean_ctor_set(v___x_3327_, 3, v___x_3325_);
return v___x_3327_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3328_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__10);
v___x_3329_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__7);
v___x_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
lean_ctor_set(v___x_3330_, 1, v___x_3328_);
return v___x_3330_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__12(void){
_start:
{
uint8_t v___x_3331_; lean_object* v___f_3332_; lean_object* v___f_3333_; lean_object* v___f_3334_; lean_object* v___x_3335_; lean_object* v___f_3336_; lean_object* v___x_3337_; 
v___x_3331_ = 1;
v___f_3332_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__4));
v___f_3333_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__3));
v___f_3334_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__2));
v___x_3335_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 9, 0);
v___f_3336_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__1));
v___x_3337_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3337_, 0, v___f_3336_);
lean_ctor_set(v___x_3337_, 1, v___x_3335_);
lean_ctor_set(v___x_3337_, 2, v___f_3334_);
lean_ctor_set(v___x_3337_, 3, v___f_3333_);
lean_ctor_set(v___x_3337_, 4, v___f_3332_);
lean_ctor_set_uint8(v___x_3337_, sizeof(void*)*5, v___x_3331_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget(lean_object* v_mvarId_3338_, lean_object* v_maxSteps_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_3343_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3347_; lean_object* v_maxDischargeDepth_3348_; uint8_t v_contextual_3349_; uint8_t v_memoize_3350_; uint8_t v_singlePass_3351_; uint8_t v_zeta_3352_; uint8_t v_beta_3353_; uint8_t v_eta_3354_; uint8_t v_etaStruct_3355_; uint8_t v_iota_3356_; uint8_t v_proj_3357_; uint8_t v_decide_3358_; uint8_t v_arith_3359_; uint8_t v_autoUnfold_3360_; uint8_t v_dsimp_3361_; uint8_t v_failIfUnchanged_3362_; uint8_t v_ground_3363_; uint8_t v_unfoldPartialApp_3364_; uint8_t v_zetaDelta_3365_; uint8_t v_index_3366_; uint8_t v_implicitDefEqProofs_3367_; uint8_t v_zetaUnused_3368_; uint8_t v_catchRuntime_3369_; uint8_t v_zetaHave_3370_; uint8_t v_letToHave_3371_; uint8_t v_congrConsts_3372_; uint8_t v_bitVecOfNat_3373_; uint8_t v_warnExponents_3374_; uint8_t v_suggestions_3375_; lean_object* v_maxSuggestions_3376_; uint8_t v_locals_3377_; uint8_t v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
v___x_3347_ = l_Lean_Meta_Simp_neutralConfig;
v_maxDischargeDepth_3348_ = lean_ctor_get(v___x_3347_, 1);
v_contextual_3349_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3);
v_memoize_3350_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 1);
v_singlePass_3351_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 2);
v_zeta_3352_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 3);
v_beta_3353_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 4);
v_eta_3354_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 5);
v_etaStruct_3355_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 6);
v_iota_3356_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 7);
v_proj_3357_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 8);
v_decide_3358_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 9);
v_arith_3359_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 10);
v_autoUnfold_3360_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 11);
v_dsimp_3361_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 12);
v_failIfUnchanged_3362_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 13);
v_ground_3363_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_3364_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 15);
v_zetaDelta_3365_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 16);
v_index_3366_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_3367_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 18);
v_zetaUnused_3368_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 19);
v_catchRuntime_3369_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 20);
v_zetaHave_3370_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 21);
v_letToHave_3371_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 22);
v_congrConsts_3372_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 23);
v_bitVecOfNat_3373_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 24);
v_warnExponents_3374_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 25);
v_suggestions_3375_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 26);
v_maxSuggestions_3376_ = lean_ctor_get(v___x_3347_, 2);
v_locals_3377_ = lean_ctor_get_uint8(v___x_3347_, sizeof(void*)*3 + 27);
v___x_3378_ = 1;
lean_inc(v_maxSuggestions_3376_);
lean_inc(v_maxDischargeDepth_3348_);
v___x_3379_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3379_, 0, v_maxSteps_3339_);
lean_ctor_set(v___x_3379_, 1, v_maxDischargeDepth_3348_);
lean_ctor_set(v___x_3379_, 2, v_maxSuggestions_3376_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3, v_contextual_3349_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 1, v_memoize_3350_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 2, v_singlePass_3351_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 3, v_zeta_3352_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 4, v_beta_3353_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 5, v_eta_3354_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 6, v_etaStruct_3355_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 7, v_iota_3356_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 8, v_proj_3357_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 9, v_decide_3358_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 10, v_arith_3359_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 11, v_autoUnfold_3360_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 12, v_dsimp_3361_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 13, v_failIfUnchanged_3362_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 14, v_ground_3363_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 15, v_unfoldPartialApp_3364_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 16, v_zetaDelta_3365_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 17, v_index_3366_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_3367_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 19, v_zetaUnused_3368_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 20, v_catchRuntime_3369_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 21, v_zetaHave_3370_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 22, v_letToHave_3371_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 23, v_congrConsts_3372_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 24, v_bitVecOfNat_3373_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 25, v_warnExponents_3374_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 26, v_suggestions_3375_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 27, v_locals_3377_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 28, v___x_3378_);
v___x_3380_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__0));
v___x_3381_ = l_Lean_Options_empty;
v___x_3382_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3379_, v___x_3380_, v_a_3346_, v___x_3381_, v_a_3340_, v_a_3342_, v_a_3343_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref_known(v___x_3382_, 1);
lean_inc(v_mvarId_3338_);
v___x_3384_ = l_Lean_MVarId_getType(v_mvarId_3338_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3386_; lean_object* v_a_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3386_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_3385_, v_a_3341_);
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc_n(v_a_3387_, 2);
lean_dec_ref(v___x_3386_);
v___x_3388_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11);
v___x_3389_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__12);
v___x_3390_ = l_Lean_Meta_Simp_main(v_a_3387_, v_a_3383_, v___x_3388_, v___x_3389_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v_fst_3392_; lean_object* v___x_3393_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3390_, 1);
v_fst_3392_ = lean_ctor_get(v_a_3391_, 0);
lean_inc(v_fst_3392_);
lean_dec(v_a_3391_);
v___x_3393_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_3338_, v_a_3387_, v_fst_3392_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
lean_dec(v_a_3387_);
return v___x_3393_;
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec(v_a_3387_);
lean_dec(v_mvarId_3338_);
v_a_3394_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3390_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3390_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec(v_a_3383_);
lean_dec(v_mvarId_3338_);
v_a_3402_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3384_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3384_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec(v_mvarId_3338_);
v_a_3410_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3382_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3382_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec(v_maxSteps_3339_);
lean_dec(v_mvarId_3338_);
v_a_3418_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3345_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3345_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___boxed(lean_object* v_mvarId_3426_, lean_object* v_maxSteps_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget(v_mvarId_3426_, v_maxSteps_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___redArg(lean_object* v_mvarId_3434_, lean_object* v_x_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3434_, v_x_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3441_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3441_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
v_a_3450_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3441_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3441_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___redArg___boxed(lean_object* v_mvarId_3458_, lean_object* v_x_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___redArg(v_mvarId_3458_, v_x_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0(lean_object* v_00_u03b1_3466_, lean_object* v_mvarId_3467_, lean_object* v_x_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v___x_3474_; 
v___x_3474_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___redArg(v_mvarId_3467_, v_x_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___boxed(lean_object* v_00_u03b1_3475_, lean_object* v_mvarId_3476_, lean_object* v_x_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0(v_00_u03b1_3475_, v_mvarId_3476_, v_x_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___lam__4(lean_object* v_maxSteps_3484_, lean_object* v_fvarId_3485_, lean_object* v___f_3486_, lean_object* v___f_3487_, lean_object* v___f_3488_, lean_object* v___f_3489_, lean_object* v_goal_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v___x_3496_; 
v___x_3496_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_3494_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3498_; lean_object* v_maxDischargeDepth_3499_; uint8_t v_contextual_3500_; uint8_t v_memoize_3501_; uint8_t v_singlePass_3502_; uint8_t v_zeta_3503_; uint8_t v_beta_3504_; uint8_t v_eta_3505_; uint8_t v_etaStruct_3506_; uint8_t v_iota_3507_; uint8_t v_proj_3508_; uint8_t v_decide_3509_; uint8_t v_arith_3510_; uint8_t v_autoUnfold_3511_; uint8_t v_dsimp_3512_; uint8_t v_failIfUnchanged_3513_; uint8_t v_ground_3514_; uint8_t v_unfoldPartialApp_3515_; uint8_t v_zetaDelta_3516_; uint8_t v_index_3517_; uint8_t v_implicitDefEqProofs_3518_; uint8_t v_zetaUnused_3519_; uint8_t v_catchRuntime_3520_; uint8_t v_zetaHave_3521_; uint8_t v_letToHave_3522_; uint8_t v_congrConsts_3523_; uint8_t v_bitVecOfNat_3524_; uint8_t v_warnExponents_3525_; uint8_t v_suggestions_3526_; lean_object* v_maxSuggestions_3527_; uint8_t v_locals_3528_; uint8_t v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
v___x_3498_ = l_Lean_Meta_Simp_neutralConfig;
v_maxDischargeDepth_3499_ = lean_ctor_get(v___x_3498_, 1);
v_contextual_3500_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3);
v_memoize_3501_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 1);
v_singlePass_3502_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 2);
v_zeta_3503_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 3);
v_beta_3504_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 4);
v_eta_3505_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 5);
v_etaStruct_3506_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 6);
v_iota_3507_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 7);
v_proj_3508_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 8);
v_decide_3509_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 9);
v_arith_3510_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 10);
v_autoUnfold_3511_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 11);
v_dsimp_3512_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 12);
v_failIfUnchanged_3513_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 13);
v_ground_3514_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_3515_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 15);
v_zetaDelta_3516_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 16);
v_index_3517_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_3518_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 18);
v_zetaUnused_3519_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 19);
v_catchRuntime_3520_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 20);
v_zetaHave_3521_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 21);
v_letToHave_3522_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 22);
v_congrConsts_3523_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 23);
v_bitVecOfNat_3524_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 24);
v_warnExponents_3525_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 25);
v_suggestions_3526_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 26);
v_maxSuggestions_3527_ = lean_ctor_get(v___x_3498_, 2);
v_locals_3528_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*3 + 27);
v___x_3529_ = 1;
lean_inc(v_maxSuggestions_3527_);
lean_inc(v_maxDischargeDepth_3499_);
v___x_3530_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3530_, 0, v_maxSteps_3484_);
lean_ctor_set(v___x_3530_, 1, v_maxDischargeDepth_3499_);
lean_ctor_set(v___x_3530_, 2, v_maxSuggestions_3527_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3, v_contextual_3500_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 1, v_memoize_3501_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 2, v_singlePass_3502_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 3, v_zeta_3503_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 4, v_beta_3504_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 5, v_eta_3505_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 6, v_etaStruct_3506_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 7, v_iota_3507_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 8, v_proj_3508_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 9, v_decide_3509_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 10, v_arith_3510_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 11, v_autoUnfold_3511_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 12, v_dsimp_3512_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 13, v_failIfUnchanged_3513_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 14, v_ground_3514_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 15, v_unfoldPartialApp_3515_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 16, v_zetaDelta_3516_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 17, v_index_3517_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_3518_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 19, v_zetaUnused_3519_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 20, v_catchRuntime_3520_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 21, v_zetaHave_3521_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 22, v_letToHave_3522_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 23, v_congrConsts_3523_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 24, v_bitVecOfNat_3524_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 25, v_warnExponents_3525_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 26, v_suggestions_3526_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 27, v_locals_3528_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*3 + 28, v___x_3529_);
v___x_3531_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__0));
v___x_3532_ = l_Lean_Options_empty;
v___x_3533_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3530_, v___x_3531_, v_a_3497_, v___x_3532_, v___y_3491_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3535_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
lean_inc(v_fvarId_3485_);
v___x_3535_ = l_Lean_FVarId_getType___redArg(v_fvarId_3485_, v___y_3491_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3537_; lean_object* v_a_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3535_, 1);
v___x_3537_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_3536_, v___y_3492_);
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref(v___x_3537_);
v___x_3539_ = lean_unsigned_to_nat(32u);
v___x_3540_ = lean_mk_empty_array_with_capacity(v___x_3539_);
lean_dec_ref(v___x_3540_);
v___x_3541_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__11);
v___x_3542_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 9, 0);
v___x_3543_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3543_, 0, v___f_3486_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
lean_ctor_set(v___x_3543_, 2, v___f_3487_);
lean_ctor_set(v___x_3543_, 3, v___f_3488_);
lean_ctor_set(v___x_3543_, 4, v___f_3489_);
lean_ctor_set_uint8(v___x_3543_, sizeof(void*)*5, v___x_3529_);
v___x_3544_ = l_Lean_Meta_Simp_main(v_a_3538_, v_a_3534_, v___x_3541_, v___x_3543_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v_fst_3546_; uint8_t v___x_3547_; lean_object* v___x_3548_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3544_, 1);
v_fst_3546_ = lean_ctor_get(v_a_3545_, 0);
lean_inc(v_fst_3546_);
lean_dec(v_a_3545_);
v___x_3547_ = 0;
v___x_3548_ = l_Lean_Meta_applySimpResultToLocalDecl(v_goal_3490_, v_fvarId_3485_, v_fst_3546_, v___x_3547_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3569_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3551_ = v___x_3548_;
v_isShared_3552_ = v_isSharedCheck_3569_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3548_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3569_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
if (lean_obj_tag(v_a_3549_) == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3555_; 
v___x_3553_ = lean_box(0);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3553_);
v___x_3555_ = v___x_3551_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
else
{
lean_object* v_val_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3568_; 
v_val_3557_ = lean_ctor_get(v_a_3549_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_a_3549_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3559_ = v_a_3549_;
v_isShared_3560_ = v_isSharedCheck_3568_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_val_3557_);
lean_dec(v_a_3549_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3568_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v_snd_3561_; lean_object* v___x_3563_; 
v_snd_3561_ = lean_ctor_get(v_val_3557_, 1);
lean_inc(v_snd_3561_);
lean_dec(v_val_3557_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v_snd_3561_);
v___x_3563_ = v___x_3559_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_snd_3561_);
v___x_3563_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3565_; 
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3563_);
v___x_3565_ = v___x_3551_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
v_a_3570_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3548_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3548_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_goal_3490_);
lean_dec(v_fvarId_3485_);
v_a_3578_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3544_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3544_);
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
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec(v_a_3534_);
lean_dec(v_goal_3490_);
lean_dec_ref(v___f_3489_);
lean_dec_ref(v___f_3488_);
lean_dec_ref(v___f_3487_);
lean_dec_ref(v___f_3486_);
lean_dec(v_fvarId_3485_);
v_a_3586_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3535_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3535_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec(v_goal_3490_);
lean_dec_ref(v___f_3489_);
lean_dec_ref(v___f_3488_);
lean_dec_ref(v___f_3487_);
lean_dec_ref(v___f_3486_);
lean_dec(v_fvarId_3485_);
v_a_3594_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3533_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3533_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec(v_goal_3490_);
lean_dec_ref(v___f_3489_);
lean_dec_ref(v___f_3488_);
lean_dec_ref(v___f_3487_);
lean_dec_ref(v___f_3486_);
lean_dec(v_fvarId_3485_);
lean_dec(v_maxSteps_3484_);
v_a_3602_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3496_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3496_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___lam__4___boxed(lean_object* v_maxSteps_3610_, lean_object* v_fvarId_3611_, lean_object* v___f_3612_, lean_object* v___f_3613_, lean_object* v___f_3614_, lean_object* v___f_3615_, lean_object* v_goal_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___lam__4(v_maxSteps_3610_, v_fvarId_3611_, v___f_3612_, v___f_3613_, v___f_3614_, v___f_3615_, v_goal_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta(lean_object* v_goal_3623_, lean_object* v_fvarId_3624_, lean_object* v_maxSteps_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_){
_start:
{
lean_object* v___f_3631_; lean_object* v___f_3632_; lean_object* v___f_3633_; lean_object* v___f_3634_; lean_object* v___f_3635_; lean_object* v___x_3636_; 
v___f_3631_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__4));
v___f_3632_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__3));
v___f_3633_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__2));
v___f_3634_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfTarget___closed__1));
lean_inc(v_goal_3623_);
v___f_3635_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___lam__4___boxed), 12, 7);
lean_closure_set(v___f_3635_, 0, v_maxSteps_3625_);
lean_closure_set(v___f_3635_, 1, v_fvarId_3624_);
lean_closure_set(v___f_3635_, 2, v___f_3634_);
lean_closure_set(v___f_3635_, 3, v___f_3633_);
lean_closure_set(v___f_3635_, 4, v___f_3632_);
lean_closure_set(v___f_3635_, 5, v___f_3631_);
lean_closure_set(v___f_3635_, 6, v_goal_3623_);
v___x_3636_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta_spec__0___redArg(v_goal_3623_, v___f_3635_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta___boxed(lean_object* v_goal_3637_, lean_object* v_fvarId_3638_, lean_object* v_maxSteps_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta(v_goal_3637_, v_fvarId_3638_, v_maxSteps_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
lean_dec(v_a_3643_);
lean_dec_ref(v_a_3642_);
lean_dec(v_a_3641_);
lean_dec_ref(v_a_3640_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(lean_object* v_x_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; 
lean_inc(v___y_3648_);
lean_inc_ref(v___y_3647_);
v___x_3654_ = lean_apply_7(v_x_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, lean_box(0));
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed(lean_object* v_x_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0(v_x_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg(lean_object* v_mvarId_3664_, lean_object* v_x_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v___f_3673_; lean_object* v___x_3674_; 
lean_inc(v___y_3667_);
lean_inc_ref(v___y_3666_);
v___f_3673_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3673_, 0, v_x_3665_);
lean_closure_set(v___f_3673_, 1, v___y_3666_);
lean_closure_set(v___f_3673_, 2, v___y_3667_);
v___x_3674_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3664_, v___f_3673_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
if (lean_obj_tag(v___x_3674_) == 0)
{
return v___x_3674_;
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3674_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3674_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg___boxed(lean_object* v_mvarId_3683_, lean_object* v_x_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg(v_mvarId_3683_, v_x_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4(lean_object* v_00_u03b1_3693_, lean_object* v_mvarId_3694_, lean_object* v_x_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg(v_mvarId_3694_, v_x_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___boxed(lean_object* v_00_u03b1_3704_, lean_object* v_mvarId_3705_, lean_object* v_x_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4(v_00_u03b1_3704_, v_mvarId_3705_, v_x_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
return v_res_3714_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(lean_object* v_a_3715_, lean_object* v_x_3716_){
_start:
{
if (lean_obj_tag(v_x_3716_) == 0)
{
uint8_t v___x_3717_; 
v___x_3717_ = 0;
return v___x_3717_;
}
else
{
lean_object* v_key_3718_; lean_object* v_tail_3719_; uint8_t v___x_3720_; 
v_key_3718_ = lean_ctor_get(v_x_3716_, 0);
v_tail_3719_ = lean_ctor_get(v_x_3716_, 2);
v___x_3720_ = l_Lean_instBEqFVarId_beq(v_key_3718_, v_a_3715_);
if (v___x_3720_ == 0)
{
v_x_3716_ = v_tail_3719_;
goto _start;
}
else
{
return v___x_3720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg___boxed(lean_object* v_a_3722_, lean_object* v_x_3723_){
_start:
{
uint8_t v_res_3724_; lean_object* v_r_3725_; 
v_res_3724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3722_, v_x_3723_);
lean_dec(v_x_3723_);
lean_dec(v_a_3722_);
v_r_3725_ = lean_box(v_res_3724_);
return v_r_3725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_x_3726_, lean_object* v_x_3727_){
_start:
{
if (lean_obj_tag(v_x_3727_) == 0)
{
return v_x_3726_;
}
else
{
lean_object* v_key_3728_; lean_object* v_value_3729_; lean_object* v_tail_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3753_; 
v_key_3728_ = lean_ctor_get(v_x_3727_, 0);
v_value_3729_ = lean_ctor_get(v_x_3727_, 1);
v_tail_3730_ = lean_ctor_get(v_x_3727_, 2);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_x_3727_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3732_ = v_x_3727_;
v_isShared_3733_ = v_isSharedCheck_3753_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_tail_3730_);
lean_inc(v_value_3729_);
lean_inc(v_key_3728_);
lean_dec(v_x_3727_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3753_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3734_; uint64_t v___x_3735_; uint64_t v___x_3736_; uint64_t v___x_3737_; uint64_t v_fold_3738_; uint64_t v___x_3739_; uint64_t v___x_3740_; uint64_t v___x_3741_; size_t v___x_3742_; size_t v___x_3743_; size_t v___x_3744_; size_t v___x_3745_; size_t v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3734_ = lean_array_get_size(v_x_3726_);
v___x_3735_ = l_Lean_instHashableFVarId_hash(v_key_3728_);
v___x_3736_ = 32ULL;
v___x_3737_ = lean_uint64_shift_right(v___x_3735_, v___x_3736_);
v_fold_3738_ = lean_uint64_xor(v___x_3735_, v___x_3737_);
v___x_3739_ = 16ULL;
v___x_3740_ = lean_uint64_shift_right(v_fold_3738_, v___x_3739_);
v___x_3741_ = lean_uint64_xor(v_fold_3738_, v___x_3740_);
v___x_3742_ = lean_uint64_to_usize(v___x_3741_);
v___x_3743_ = lean_usize_of_nat(v___x_3734_);
v___x_3744_ = ((size_t)1ULL);
v___x_3745_ = lean_usize_sub(v___x_3743_, v___x_3744_);
v___x_3746_ = lean_usize_land(v___x_3742_, v___x_3745_);
v___x_3747_ = lean_array_uget_borrowed(v_x_3726_, v___x_3746_);
lean_inc(v___x_3747_);
if (v_isShared_3733_ == 0)
{
lean_ctor_set(v___x_3732_, 2, v___x_3747_);
v___x_3749_ = v___x_3732_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_key_3728_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_value_3729_);
lean_ctor_set(v_reuseFailAlloc_3752_, 2, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_array_uset(v_x_3726_, v___x_3746_, v___x_3749_);
v_x_3726_ = v___x_3750_;
v_x_3727_ = v_tail_3730_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(lean_object* v_i_3754_, lean_object* v_source_3755_, lean_object* v_target_3756_){
_start:
{
lean_object* v___x_3757_; uint8_t v___x_3758_; 
v___x_3757_ = lean_array_get_size(v_source_3755_);
v___x_3758_ = lean_nat_dec_lt(v_i_3754_, v___x_3757_);
if (v___x_3758_ == 0)
{
lean_dec_ref(v_source_3755_);
lean_dec(v_i_3754_);
return v_target_3756_;
}
else
{
lean_object* v_es_3759_; lean_object* v___x_3760_; lean_object* v_source_3761_; lean_object* v_target_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_es_3759_ = lean_array_fget(v_source_3755_, v_i_3754_);
v___x_3760_ = lean_box(0);
v_source_3761_ = lean_array_fset(v_source_3755_, v_i_3754_, v___x_3760_);
v_target_3762_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(v_target_3756_, v_es_3759_);
v___x_3763_ = lean_unsigned_to_nat(1u);
v___x_3764_ = lean_nat_add(v_i_3754_, v___x_3763_);
lean_dec(v_i_3754_);
v_i_3754_ = v___x_3764_;
v_source_3755_ = v_source_3761_;
v_target_3756_ = v_target_3762_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(lean_object* v_data_3766_){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v_nbuckets_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3767_ = lean_array_get_size(v_data_3766_);
v___x_3768_ = lean_unsigned_to_nat(2u);
v_nbuckets_3769_ = lean_nat_mul(v___x_3767_, v___x_3768_);
v___x_3770_ = lean_unsigned_to_nat(0u);
v___x_3771_ = lean_box(0);
v___x_3772_ = lean_mk_array(v_nbuckets_3769_, v___x_3771_);
v___x_3773_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(v___x_3770_, v_data_3766_, v___x_3772_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_m_3774_, lean_object* v_a_3775_, lean_object* v_b_3776_){
_start:
{
lean_object* v_size_3777_; lean_object* v_buckets_3778_; lean_object* v___x_3779_; uint64_t v___x_3780_; uint64_t v___x_3781_; uint64_t v___x_3782_; uint64_t v_fold_3783_; uint64_t v___x_3784_; uint64_t v___x_3785_; uint64_t v___x_3786_; size_t v___x_3787_; size_t v___x_3788_; size_t v___x_3789_; size_t v___x_3790_; size_t v___x_3791_; lean_object* v_bkt_3792_; uint8_t v___x_3793_; 
v_size_3777_ = lean_ctor_get(v_m_3774_, 0);
v_buckets_3778_ = lean_ctor_get(v_m_3774_, 1);
v___x_3779_ = lean_array_get_size(v_buckets_3778_);
v___x_3780_ = l_Lean_instHashableFVarId_hash(v_a_3775_);
v___x_3781_ = 32ULL;
v___x_3782_ = lean_uint64_shift_right(v___x_3780_, v___x_3781_);
v_fold_3783_ = lean_uint64_xor(v___x_3780_, v___x_3782_);
v___x_3784_ = 16ULL;
v___x_3785_ = lean_uint64_shift_right(v_fold_3783_, v___x_3784_);
v___x_3786_ = lean_uint64_xor(v_fold_3783_, v___x_3785_);
v___x_3787_ = lean_uint64_to_usize(v___x_3786_);
v___x_3788_ = lean_usize_of_nat(v___x_3779_);
v___x_3789_ = ((size_t)1ULL);
v___x_3790_ = lean_usize_sub(v___x_3788_, v___x_3789_);
v___x_3791_ = lean_usize_land(v___x_3787_, v___x_3790_);
v_bkt_3792_ = lean_array_uget_borrowed(v_buckets_3778_, v___x_3791_);
v___x_3793_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3775_, v_bkt_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3814_; 
lean_inc_ref(v_buckets_3778_);
lean_inc(v_size_3777_);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_m_3774_);
if (v_isSharedCheck_3814_ == 0)
{
lean_object* v_unused_3815_; lean_object* v_unused_3816_; 
v_unused_3815_ = lean_ctor_get(v_m_3774_, 1);
lean_dec(v_unused_3815_);
v_unused_3816_ = lean_ctor_get(v_m_3774_, 0);
lean_dec(v_unused_3816_);
v___x_3795_ = v_m_3774_;
v_isShared_3796_ = v_isSharedCheck_3814_;
goto v_resetjp_3794_;
}
else
{
lean_dec(v_m_3774_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3814_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3797_; lean_object* v_size_x27_3798_; lean_object* v___x_3799_; lean_object* v_buckets_x27_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; uint8_t v___x_3806_; 
v___x_3797_ = lean_unsigned_to_nat(1u);
v_size_x27_3798_ = lean_nat_add(v_size_3777_, v___x_3797_);
lean_dec(v_size_3777_);
lean_inc(v_bkt_3792_);
v___x_3799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3799_, 0, v_a_3775_);
lean_ctor_set(v___x_3799_, 1, v_b_3776_);
lean_ctor_set(v___x_3799_, 2, v_bkt_3792_);
v_buckets_x27_3800_ = lean_array_uset(v_buckets_3778_, v___x_3791_, v___x_3799_);
v___x_3801_ = lean_unsigned_to_nat(4u);
v___x_3802_ = lean_nat_mul(v_size_x27_3798_, v___x_3801_);
v___x_3803_ = lean_unsigned_to_nat(3u);
v___x_3804_ = lean_nat_div(v___x_3802_, v___x_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_array_get_size(v_buckets_x27_3800_);
v___x_3806_ = lean_nat_dec_le(v___x_3804_, v___x_3805_);
lean_dec(v___x_3804_);
if (v___x_3806_ == 0)
{
lean_object* v_val_3807_; lean_object* v___x_3809_; 
v_val_3807_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(v_buckets_x27_3800_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 1, v_val_3807_);
lean_ctor_set(v___x_3795_, 0, v_size_x27_3798_);
v___x_3809_ = v___x_3795_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_size_x27_3798_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v_val_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
else
{
lean_object* v___x_3812_; 
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 1, v_buckets_x27_3800_);
lean_ctor_set(v___x_3795_, 0, v_size_x27_3798_);
v___x_3812_ = v___x_3795_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_size_x27_3798_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_buckets_x27_3800_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
else
{
lean_dec(v_b_3776_);
lean_dec(v_a_3775_);
return v_m_3774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(lean_object* v_as_3817_, size_t v_i_3818_, size_t v_stop_3819_, lean_object* v_b_3820_, lean_object* v___y_3821_){
_start:
{
uint8_t v___x_3823_; 
v___x_3823_ = lean_usize_dec_eq(v_i_3818_, v_stop_3819_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v_rewriteCache_3825_; lean_object* v_acNfCache_3826_; lean_object* v_typeAnalysis_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3841_; 
v___x_3824_ = lean_st_ref_take(v___y_3821_);
v_rewriteCache_3825_ = lean_ctor_get(v___x_3824_, 0);
v_acNfCache_3826_ = lean_ctor_get(v___x_3824_, 1);
v_typeAnalysis_3827_ = lean_ctor_get(v___x_3824_, 2);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3829_ = v___x_3824_;
v_isShared_3830_ = v_isSharedCheck_3841_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_typeAnalysis_3827_);
lean_inc(v_acNfCache_3826_);
lean_inc(v_rewriteCache_3825_);
lean_dec(v___x_3824_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3841_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3835_; 
v___x_3831_ = lean_array_uget_borrowed(v_as_3817_, v_i_3818_);
v___x_3832_ = lean_box(0);
lean_inc(v___x_3831_);
v___x_3833_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_acNfCache_3826_, v___x_3831_, v___x_3832_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 1, v___x_3833_);
v___x_3835_ = v___x_3829_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_rewriteCache_3825_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v___x_3833_);
lean_ctor_set(v_reuseFailAlloc_3840_, 2, v_typeAnalysis_3827_);
v___x_3835_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
lean_object* v___x_3836_; size_t v___x_3837_; size_t v___x_3838_; 
v___x_3836_ = lean_st_ref_set(v___y_3821_, v___x_3835_);
v___x_3837_ = ((size_t)1ULL);
v___x_3838_ = lean_usize_add(v_i_3818_, v___x_3837_);
v_i_3818_ = v___x_3838_;
v_b_3820_ = v___x_3832_;
goto _start;
}
}
}
else
{
lean_object* v___x_3842_; 
v___x_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3842_, 0, v_b_3820_);
return v___x_3842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg___boxed(lean_object* v_as_3843_, lean_object* v_i_3844_, lean_object* v_stop_3845_, lean_object* v_b_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
size_t v_i_boxed_3849_; size_t v_stop_boxed_3850_; lean_object* v_res_3851_; 
v_i_boxed_3849_ = lean_unbox_usize(v_i_3844_);
lean_dec(v_i_3844_);
v_stop_boxed_3850_ = lean_unbox_usize(v_stop_3845_);
lean_dec(v_stop_3845_);
v_res_3851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(v_as_3843_, v_i_boxed_3849_, v_stop_boxed_3850_, v_b_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v_as_3843_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object* v___x_3852_, size_t v___x_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = l_Lean_Meta_getPropHyps(v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3880_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3864_ = v___x_3861_;
v_isShared_3865_ = v_isSharedCheck_3880_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3880_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; uint8_t v___x_3868_; 
v___x_3866_ = lean_array_get_size(v_a_3862_);
v___x_3867_ = lean_box(0);
v___x_3868_ = lean_nat_dec_lt(v___x_3852_, v___x_3866_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3870_; 
lean_dec(v_a_3862_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v___x_3867_);
v___x_3870_ = v___x_3864_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3867_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
else
{
uint8_t v___x_3872_; 
v___x_3872_ = lean_nat_dec_le(v___x_3866_, v___x_3866_);
if (v___x_3872_ == 0)
{
if (v___x_3868_ == 0)
{
lean_object* v___x_3874_; 
lean_dec(v_a_3862_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 0, v___x_3867_);
v___x_3874_ = v___x_3864_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3867_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
else
{
size_t v___x_3876_; lean_object* v___x_3877_; 
lean_del_object(v___x_3864_);
v___x_3876_ = lean_usize_of_nat(v___x_3866_);
v___x_3877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(v_a_3862_, v___x_3853_, v___x_3876_, v___x_3867_, v___y_3855_);
lean_dec(v_a_3862_);
return v___x_3877_;
}
}
else
{
size_t v___x_3878_; lean_object* v___x_3879_; 
lean_del_object(v___x_3864_);
v___x_3878_ = lean_usize_of_nat(v___x_3866_);
v___x_3879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(v_a_3862_, v___x_3853_, v___x_3878_, v___x_3867_, v___y_3855_);
lean_dec(v_a_3862_);
return v___x_3879_;
}
}
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
v_a_3881_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3861_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3861_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v___x_3889_, lean_object* v___x_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
size_t v___x_8265__boxed_3898_; lean_object* v_res_3899_; 
v___x_8265__boxed_3898_ = lean_unbox_usize(v___x_3890_);
lean_dec(v___x_3890_);
v_res_3899_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(v___x_3889_, v___x_8265__boxed_3898_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___x_3889_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_as_3900_, size_t v_sz_3901_, size_t v_i_3902_, lean_object* v_b_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
uint8_t v___x_3910_; 
v___x_3910_ = lean_usize_dec_lt(v_i_3902_, v_sz_3901_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3911_, 0, v_b_3903_);
return v___x_3911_;
}
else
{
lean_object* v_maxSteps_3912_; lean_object* v_a_3913_; lean_object* v___x_3914_; 
v_maxSteps_3912_ = lean_ctor_get(v___y_3904_, 1);
v_a_3913_ = lean_array_uget_borrowed(v_as_3900_, v_i_3902_);
lean_inc(v_maxSteps_3912_);
lean_inc(v_a_3913_);
lean_inc(v_b_3903_);
v___x_3914_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfHypMeta(v_b_3903_, v_a_3913_, v_maxSteps_3912_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v_a_3917_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3914_, 1);
if (lean_obj_tag(v_a_3915_) == 1)
{
lean_object* v_val_3921_; 
lean_dec(v_b_3903_);
v_val_3921_ = lean_ctor_get(v_a_3915_, 0);
lean_inc(v_val_3921_);
lean_dec_ref_known(v_a_3915_, 1);
v_a_3917_ = v_val_3921_;
goto v___jp_3916_;
}
else
{
lean_dec(v_a_3915_);
v_a_3917_ = v_b_3903_;
goto v___jp_3916_;
}
v___jp_3916_:
{
size_t v___x_3918_; size_t v___x_3919_; 
v___x_3918_ = ((size_t)1ULL);
v___x_3919_ = lean_usize_add(v_i_3902_, v___x_3918_);
v_i_3902_ = v___x_3919_;
v_b_3903_ = v_a_3917_;
goto _start;
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_dec(v_b_3903_);
v_a_3922_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3914_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3914_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_as_3930_, lean_object* v_sz_3931_, lean_object* v_i_3932_, lean_object* v_b_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
size_t v_sz_boxed_3940_; size_t v_i_boxed_3941_; lean_object* v_res_3942_; 
v_sz_boxed_3940_ = lean_unbox_usize(v_sz_3931_);
lean_dec(v_sz_3931_);
v_i_boxed_3941_ = lean_unbox_usize(v_i_3932_);
lean_dec(v_i_3932_);
v_res_3942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_as_3930_, v_sz_boxed_3940_, v_i_boxed_3941_, v_b_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec_ref(v_as_3930_);
return v_res_3942_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_m_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v_buckets_3945_; lean_object* v___x_3946_; uint64_t v___x_3947_; uint64_t v___x_3948_; uint64_t v___x_3949_; uint64_t v_fold_3950_; uint64_t v___x_3951_; uint64_t v___x_3952_; uint64_t v___x_3953_; size_t v___x_3954_; size_t v___x_3955_; size_t v___x_3956_; size_t v___x_3957_; size_t v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v_buckets_3945_ = lean_ctor_get(v_m_3943_, 1);
v___x_3946_ = lean_array_get_size(v_buckets_3945_);
v___x_3947_ = l_Lean_instHashableFVarId_hash(v_a_3944_);
v___x_3948_ = 32ULL;
v___x_3949_ = lean_uint64_shift_right(v___x_3947_, v___x_3948_);
v_fold_3950_ = lean_uint64_xor(v___x_3947_, v___x_3949_);
v___x_3951_ = 16ULL;
v___x_3952_ = lean_uint64_shift_right(v_fold_3950_, v___x_3951_);
v___x_3953_ = lean_uint64_xor(v_fold_3950_, v___x_3952_);
v___x_3954_ = lean_uint64_to_usize(v___x_3953_);
v___x_3955_ = lean_usize_of_nat(v___x_3946_);
v___x_3956_ = ((size_t)1ULL);
v___x_3957_ = lean_usize_sub(v___x_3955_, v___x_3956_);
v___x_3958_ = lean_usize_land(v___x_3954_, v___x_3957_);
v___x_3959_ = lean_array_uget_borrowed(v_buckets_3945_, v___x_3958_);
v___x_3960_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_3944_, v___x_3959_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_m_3961_, lean_object* v_a_3962_){
_start:
{
uint8_t v_res_3963_; lean_object* v_r_3964_; 
v_res_3963_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_m_3961_, v_a_3962_);
lean_dec(v_a_3962_);
lean_dec_ref(v_m_3961_);
v_r_3964_ = lean_box(v_res_3963_);
return v_r_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg(lean_object* v_as_3965_, size_t v_i_3966_, size_t v_stop_3967_, lean_object* v_b_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_a_3972_; uint8_t v___x_3976_; 
v___x_3976_ = lean_usize_dec_eq(v_i_3966_, v_stop_3967_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; lean_object* v_acNfCache_3978_; lean_object* v___x_3979_; uint8_t v___x_3980_; uint8_t v___x_3981_; 
v___x_3977_ = lean_st_ref_get(v___y_3969_);
v_acNfCache_3978_ = lean_ctor_get(v___x_3977_, 1);
lean_inc_ref(v_acNfCache_3978_);
lean_dec(v___x_3977_);
v___x_3979_ = lean_array_uget_borrowed(v_as_3965_, v_i_3966_);
v___x_3980_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_acNfCache_3978_, v___x_3979_);
lean_dec_ref(v_acNfCache_3978_);
v___x_3981_ = lean_bool_not(v___x_3980_);
if (v___x_3981_ == 0)
{
v_a_3972_ = v_b_3968_;
goto v___jp_3971_;
}
else
{
lean_object* v___x_3982_; 
lean_inc(v___x_3979_);
v___x_3982_ = lean_array_push(v_b_3968_, v___x_3979_);
v_a_3972_ = v___x_3982_;
goto v___jp_3971_;
}
}
else
{
lean_object* v___x_3983_; 
v___x_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3983_, 0, v_b_3968_);
return v___x_3983_;
}
v___jp_3971_:
{
size_t v___x_3973_; size_t v___x_3974_; 
v___x_3973_ = ((size_t)1ULL);
v___x_3974_ = lean_usize_add(v_i_3966_, v___x_3973_);
v_i_3966_ = v___x_3974_;
v_b_3968_ = v_a_3972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg___boxed(lean_object* v_as_3984_, lean_object* v_i_3985_, lean_object* v_stop_3986_, lean_object* v_b_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
size_t v_i_boxed_3990_; size_t v_stop_boxed_3991_; lean_object* v_res_3992_; 
v_i_boxed_3990_ = lean_unbox_usize(v_i_3985_);
lean_dec(v_i_3985_);
v_stop_boxed_3991_ = lean_unbox_usize(v_stop_3986_);
lean_dec(v_stop_3986_);
v_res_3992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg(v_as_3984_, v_i_boxed_3990_, v_stop_boxed_3991_, v_b_3987_, v___y_3988_);
lean_dec(v___y_3988_);
lean_dec_ref(v_as_3984_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object* v_goal_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l_Lean_Meta_getPropHyps(v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4010_; lean_object* v_a_4012_; lean_object* v___y_4045_; lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v___x_4010_ = lean_unsigned_to_nat(0u);
v___x_4055_ = lean_array_get_size(v_a_4009_);
v___x_4056_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__1));
v___x_4057_ = lean_nat_dec_lt(v___x_4010_, v___x_4055_);
if (v___x_4057_ == 0)
{
lean_dec(v_a_4009_);
v_a_4012_ = v___x_4056_;
goto v___jp_4011_;
}
else
{
uint8_t v___x_4058_; 
v___x_4058_ = lean_nat_dec_le(v___x_4055_, v___x_4055_);
if (v___x_4058_ == 0)
{
if (v___x_4057_ == 0)
{
lean_dec(v_a_4009_);
v_a_4012_ = v___x_4056_;
goto v___jp_4011_;
}
else
{
size_t v___x_4059_; size_t v___x_4060_; lean_object* v___x_4061_; 
v___x_4059_ = ((size_t)0ULL);
v___x_4060_ = lean_usize_of_nat(v___x_4055_);
v___x_4061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg(v_a_4009_, v___x_4059_, v___x_4060_, v___x_4056_, v___y_4002_);
lean_dec(v_a_4009_);
v___y_4045_ = v___x_4061_;
goto v___jp_4044_;
}
}
else
{
size_t v___x_4062_; size_t v___x_4063_; lean_object* v___x_4064_; 
v___x_4062_ = ((size_t)0ULL);
v___x_4063_ = lean_usize_of_nat(v___x_4055_);
v___x_4064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg(v_a_4009_, v___x_4062_, v___x_4063_, v___x_4056_, v___y_4002_);
lean_dec(v_a_4009_);
v___y_4045_ = v___x_4064_;
goto v___jp_4044_;
}
}
v___jp_4011_:
{
size_t v_sz_4013_; size_t v___x_4014_; lean_object* v___x_4015_; 
v_sz_4013_ = lean_array_size(v_a_4012_);
v___x_4014_ = ((size_t)0ULL);
v___x_4015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_a_4012_, v_sz_4013_, v___x_4014_, v_goal_4000_, v___y_4001_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
lean_dec_ref(v_a_4012_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___f_4017_; lean_object* v___x_4018_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc_n(v_a_4016_, 2);
lean_dec_ref_known(v___x_4015_, 1);
v___f_4017_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___closed__0));
v___x_4018_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg(v_a_4016_, v___f_4017_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4026_; 
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4026_ == 0)
{
lean_object* v_unused_4027_; 
v_unused_4027_ = lean_ctor_get(v___x_4018_, 0);
lean_dec(v_unused_4027_);
v___x_4020_ = v___x_4018_;
v_isShared_4021_ = v_isSharedCheck_4026_;
goto v_resetjp_4019_;
}
else
{
lean_dec(v___x_4018_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4026_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4022_, 0, v_a_4016_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v___x_4022_);
v___x_4024_ = v___x_4020_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec(v_a_4016_);
v_a_4028_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4018_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4018_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
v_a_4036_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4015_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4015_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
v___jp_4044_:
{
if (lean_obj_tag(v___y_4045_) == 0)
{
lean_object* v_a_4046_; 
v_a_4046_ = lean_ctor_get(v___y_4045_, 0);
lean_inc(v_a_4046_);
lean_dec_ref_known(v___y_4045_, 1);
v_a_4012_ = v_a_4046_;
goto v___jp_4011_;
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_dec(v_goal_4000_);
v_a_4047_ = lean_ctor_get(v___y_4045_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___y_4045_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___y_4045_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___y_4045_);
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
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec(v_goal_4000_);
v_a_4065_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4008_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4008_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v_goal_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(v_goal_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__2(lean_object* v_goal_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v___f_4090_; lean_object* v___x_4091_; 
lean_inc(v_goal_4082_);
v___f_4090_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4090_, 0, v_goal_4082_);
v___x_4091_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__4___redArg(v_goal_4082_, v___f_4090_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__2___boxed(lean_object* v_goal_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__2(v_goal_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
return v_res_4100_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object* v_00_u03b2_4109_, lean_object* v_m_4110_, lean_object* v_a_4111_){
_start:
{
uint8_t v___x_4112_; 
v___x_4112_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_m_4110_, v_a_4111_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_00_u03b2_4113_, lean_object* v_m_4114_, lean_object* v_a_4115_){
_start:
{
uint8_t v_res_4116_; lean_object* v_r_4117_; 
v_res_4116_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(v_00_u03b2_4113_, v_m_4114_, v_a_4115_);
lean_dec(v_a_4115_);
lean_dec_ref(v_m_4114_);
v_r_4117_ = lean_box(v_res_4116_);
return v_r_4117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object* v_00_u03b2_4118_, lean_object* v_m_4119_, lean_object* v_a_4120_, lean_object* v_b_4121_){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_m_4119_, v_a_4120_, v_b_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object* v_as_4123_, size_t v_sz_4124_, size_t v_i_4125_, lean_object* v_b_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v___x_4134_; 
v___x_4134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_as_4123_, v_sz_4124_, v_i_4125_, v_b_4126_, v___y_4127_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_as_4135_, lean_object* v_sz_4136_, lean_object* v_i_4137_, lean_object* v_b_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
size_t v_sz_boxed_4146_; size_t v_i_boxed_4147_; lean_object* v_res_4148_; 
v_sz_boxed_4146_ = lean_unbox_usize(v_sz_4136_);
lean_dec(v_sz_4136_);
v_i_boxed_4147_ = lean_unbox_usize(v_i_4137_);
lean_dec(v_i_4137_);
v_res_4148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(v_as_4135_, v_sz_boxed_4146_, v_i_boxed_4147_, v_b_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec_ref(v_as_4135_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3(lean_object* v_as_4149_, size_t v_i_4150_, size_t v_stop_4151_, lean_object* v_b_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(v_as_4149_, v_i_4150_, v_stop_4151_, v_b_4152_, v___y_4154_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___boxed(lean_object* v_as_4161_, lean_object* v_i_4162_, lean_object* v_stop_4163_, lean_object* v_b_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
size_t v_i_boxed_4172_; size_t v_stop_boxed_4173_; lean_object* v_res_4174_; 
v_i_boxed_4172_ = lean_unbox_usize(v_i_4162_);
lean_dec(v_i_4162_);
v_stop_boxed_4173_ = lean_unbox_usize(v_stop_4163_);
lean_dec(v_stop_4163_);
v_res_4174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3(v_as_4161_, v_i_boxed_4172_, v_stop_boxed_4173_, v_b_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec_ref(v_as_4161_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5(lean_object* v_as_4175_, size_t v_i_4176_, size_t v_stop_4177_, lean_object* v_b_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___redArg(v_as_4175_, v_i_4176_, v_stop_4177_, v_b_4178_, v___y_4180_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5___boxed(lean_object* v_as_4187_, lean_object* v_i_4188_, lean_object* v_stop_4189_, lean_object* v_b_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
size_t v_i_boxed_4198_; size_t v_stop_boxed_4199_; lean_object* v_res_4200_; 
v_i_boxed_4198_ = lean_unbox_usize(v_i_4188_);
lean_dec(v_i_4188_);
v_stop_boxed_4199_ = lean_unbox_usize(v_stop_4189_);
lean_dec(v_stop_4189_);
v_res_4200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__5(v_as_4187_, v_i_boxed_4198_, v_stop_boxed_4199_, v_b_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec_ref(v_as_4187_);
return v_res_4200_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0(lean_object* v_00_u03b2_4201_, lean_object* v_a_4202_, lean_object* v_x_4203_){
_start:
{
uint8_t v___x_4204_; 
v___x_4204_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___redArg(v_a_4202_, v_x_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4205_, lean_object* v_a_4206_, lean_object* v_x_4207_){
_start:
{
uint8_t v_res_4208_; lean_object* v_r_4209_; 
v_res_4208_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_spec__0(v_00_u03b2_4205_, v_a_4206_, v_x_4207_);
lean_dec(v_x_4207_);
lean_dec(v_a_4206_);
v_r_4209_ = lean_box(v_res_4208_);
return v_r_4209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2(lean_object* v_00_u03b2_4210_, lean_object* v_data_4211_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2___redArg(v_data_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4213_, lean_object* v_i_4214_, lean_object* v_source_4215_, lean_object* v_target_4216_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4___redArg(v_i_4214_, v_source_4215_, v_target_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b2_4218_, lean_object* v_x_4219_, lean_object* v_x_4220_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__2_spec__4_spec__8___redArg(v_x_4219_, v_x_4220_);
return v___x_4221_;
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
