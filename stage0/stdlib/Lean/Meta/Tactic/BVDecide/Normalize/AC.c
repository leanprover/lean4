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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_AC_rewriteUnnormalizedRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_checkEmoji;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "canonicalizeWithSharing"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Operations mismatch:\n      the left-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n        "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\n      but the right-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Canonicalizing with respect to operation: '"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to recognize operation: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object**);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Canonicalizing: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_ac_nf "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " found `BEq.beq`."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " found `Eq`."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bv_ac_nf"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 2, 240, 42, 244, 93, 182, 215)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(lean_object* v_x_165_, lean_object* v_s_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_174_; 
lean_inc(v_a_172_);
lean_inc_ref(v_a_171_);
lean_inc(v_a_170_);
lean_inc_ref(v_a_169_);
lean_inc(v_a_168_);
lean_inc_ref(v_a_167_);
v___x_174_ = lean_apply_8(v_x_165_, v_s_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, lean_box(0));
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_183_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v_fst_179_; lean_object* v___x_181_; 
v_fst_179_ = lean_ctor_get(v_a_175_, 0);
lean_inc(v_fst_179_);
lean_dec(v_a_175_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v_fst_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_fst_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
v_a_184_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_174_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_174_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg___boxed(lean_object* v_x_192_, lean_object* v_s_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v_x_192_, v_s_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(lean_object* v_00_u03b1_202_, lean_object* v_x_203_, lean_object* v_s_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v_x_203_, v_s_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___boxed(lean_object* v_00_u03b1_213_, lean_object* v_x_214_, lean_object* v_s_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(v_00_u03b1_213_, v_x_214_, v_s_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(lean_object* v_a_224_, lean_object* v_b_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_dec(v_b_225_);
lean_dec_ref(v_a_224_);
return v_x_226_;
}
else
{
lean_object* v_key_227_; lean_object* v_value_228_; lean_object* v_tail_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_241_; 
v_key_227_ = lean_ctor_get(v_x_226_, 0);
v_value_228_ = lean_ctor_get(v_x_226_, 1);
v_tail_229_ = lean_ctor_get(v_x_226_, 2);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_241_ == 0)
{
v___x_231_ = v_x_226_;
v_isShared_232_ = v_isSharedCheck_241_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_tail_229_);
lean_inc(v_value_228_);
lean_inc(v_key_227_);
lean_dec(v_x_226_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_241_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
uint8_t v___x_233_; 
v___x_233_ = lean_expr_eqv(v_key_227_, v_a_224_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_224_, v_b_225_, v_tail_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 2, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_key_227_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_value_228_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
else
{
lean_object* v___x_239_; 
lean_dec(v_value_228_);
lean_dec(v_key_227_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 1, v_b_225_);
lean_ctor_set(v___x_231_, 0, v_a_224_);
v___x_239_ = v___x_231_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_224_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_b_225_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_tail_229_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object* v_a_242_, lean_object* v_x_243_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
uint8_t v___x_244_; 
v___x_244_ = 0;
return v___x_244_;
}
else
{
lean_object* v_key_245_; lean_object* v_tail_246_; uint8_t v___x_247_; 
v_key_245_ = lean_ctor_get(v_x_243_, 0);
v_tail_246_ = lean_ctor_get(v_x_243_, 2);
v___x_247_ = lean_expr_eqv(v_key_245_, v_a_242_);
if (v___x_247_ == 0)
{
v_x_243_ = v_tail_246_;
goto _start;
}
else
{
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object* v_a_249_, lean_object* v_x_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_249_, v_x_250_);
lean_dec(v_x_250_);
lean_dec_ref(v_a_249_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
return v_x_253_;
}
else
{
lean_object* v_key_255_; lean_object* v_value_256_; lean_object* v_tail_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_280_; 
v_key_255_ = lean_ctor_get(v_x_254_, 0);
v_value_256_ = lean_ctor_get(v_x_254_, 1);
v_tail_257_ = lean_ctor_get(v_x_254_, 2);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_280_ == 0)
{
v___x_259_ = v_x_254_;
v_isShared_260_ = v_isSharedCheck_280_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_tail_257_);
lean_inc(v_value_256_);
lean_inc(v_key_255_);
lean_dec(v_x_254_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_280_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; uint64_t v___x_262_; uint64_t v___x_263_; uint64_t v___x_264_; uint64_t v_fold_265_; uint64_t v___x_266_; uint64_t v___x_267_; uint64_t v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_261_ = lean_array_get_size(v_x_253_);
v___x_262_ = l_Lean_Expr_hash(v_key_255_);
v___x_263_ = 32ULL;
v___x_264_ = lean_uint64_shift_right(v___x_262_, v___x_263_);
v_fold_265_ = lean_uint64_xor(v___x_262_, v___x_264_);
v___x_266_ = 16ULL;
v___x_267_ = lean_uint64_shift_right(v_fold_265_, v___x_266_);
v___x_268_ = lean_uint64_xor(v_fold_265_, v___x_267_);
v___x_269_ = lean_uint64_to_usize(v___x_268_);
v___x_270_ = lean_usize_of_nat(v___x_261_);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_sub(v___x_270_, v___x_271_);
v___x_273_ = lean_usize_land(v___x_269_, v___x_272_);
v___x_274_ = lean_array_uget_borrowed(v_x_253_, v___x_273_);
lean_inc(v___x_274_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 2, v___x_274_);
v___x_276_ = v___x_259_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_key_255_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_value_256_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v___x_274_);
v___x_276_ = v_reuseFailAlloc_279_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; 
v___x_277_ = lean_array_uset(v_x_253_, v___x_273_, v___x_276_);
v_x_253_ = v___x_277_;
v_x_254_ = v_tail_257_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(lean_object* v_i_281_, lean_object* v_source_282_, lean_object* v_target_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_array_get_size(v_source_282_);
v___x_285_ = lean_nat_dec_lt(v_i_281_, v___x_284_);
if (v___x_285_ == 0)
{
lean_dec_ref(v_source_282_);
lean_dec(v_i_281_);
return v_target_283_;
}
else
{
lean_object* v_es_286_; lean_object* v___x_287_; lean_object* v_source_288_; lean_object* v_target_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_es_286_ = lean_array_fget(v_source_282_, v_i_281_);
v___x_287_ = lean_box(0);
v_source_288_ = lean_array_fset(v_source_282_, v_i_281_, v___x_287_);
v_target_289_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_283_, v_es_286_);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_add(v_i_281_, v___x_290_);
lean_dec(v_i_281_);
v_i_281_ = v___x_291_;
v_source_282_ = v_source_288_;
v_target_283_ = v_target_289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(lean_object* v_data_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_nbuckets_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_294_ = lean_array_get_size(v_data_293_);
v___x_295_ = lean_unsigned_to_nat(2u);
v_nbuckets_296_ = lean_nat_mul(v___x_294_, v___x_295_);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_box(0);
v___x_299_ = lean_mk_array(v_nbuckets_296_, v___x_298_);
v___x_300_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v___x_297_, v_data_293_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object* v_m_301_, lean_object* v_a_302_, lean_object* v_b_303_){
_start:
{
lean_object* v_size_304_; lean_object* v_buckets_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_348_; 
v_size_304_ = lean_ctor_get(v_m_301_, 0);
v_buckets_305_ = lean_ctor_get(v_m_301_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_m_301_);
if (v_isSharedCheck_348_ == 0)
{
v___x_307_ = v_m_301_;
v_isShared_308_ = v_isSharedCheck_348_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_buckets_305_);
lean_inc(v_size_304_);
lean_dec(v_m_301_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_348_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; uint64_t v___x_310_; uint64_t v___x_311_; uint64_t v___x_312_; uint64_t v_fold_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; lean_object* v_bkt_322_; uint8_t v___x_323_; 
v___x_309_ = lean_array_get_size(v_buckets_305_);
v___x_310_ = l_Lean_Expr_hash(v_a_302_);
v___x_311_ = 32ULL;
v___x_312_ = lean_uint64_shift_right(v___x_310_, v___x_311_);
v_fold_313_ = lean_uint64_xor(v___x_310_, v___x_312_);
v___x_314_ = 16ULL;
v___x_315_ = lean_uint64_shift_right(v_fold_313_, v___x_314_);
v___x_316_ = lean_uint64_xor(v_fold_313_, v___x_315_);
v___x_317_ = lean_uint64_to_usize(v___x_316_);
v___x_318_ = lean_usize_of_nat(v___x_309_);
v___x_319_ = ((size_t)1ULL);
v___x_320_ = lean_usize_sub(v___x_318_, v___x_319_);
v___x_321_ = lean_usize_land(v___x_317_, v___x_320_);
v_bkt_322_ = lean_array_uget_borrowed(v_buckets_305_, v___x_321_);
v___x_323_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_302_, v_bkt_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v_size_x27_325_; lean_object* v___x_326_; lean_object* v_buckets_x27_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_324_ = lean_unsigned_to_nat(1u);
v_size_x27_325_ = lean_nat_add(v_size_304_, v___x_324_);
lean_dec(v_size_304_);
lean_inc(v_bkt_322_);
v___x_326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_326_, 0, v_a_302_);
lean_ctor_set(v___x_326_, 1, v_b_303_);
lean_ctor_set(v___x_326_, 2, v_bkt_322_);
v_buckets_x27_327_ = lean_array_uset(v_buckets_305_, v___x_321_, v___x_326_);
v___x_328_ = lean_unsigned_to_nat(4u);
v___x_329_ = lean_nat_mul(v_size_x27_325_, v___x_328_);
v___x_330_ = lean_unsigned_to_nat(3u);
v___x_331_ = lean_nat_div(v___x_329_, v___x_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_array_get_size(v_buckets_x27_327_);
v___x_333_ = lean_nat_dec_le(v___x_331_, v___x_332_);
lean_dec(v___x_331_);
if (v___x_333_ == 0)
{
lean_object* v_val_334_; lean_object* v___x_336_; 
v_val_334_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_buckets_x27_327_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v_val_334_);
lean_ctor_set(v___x_307_, 0, v_size_x27_325_);
v___x_336_ = v___x_307_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_size_x27_325_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_val_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
else
{
lean_object* v___x_339_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v_buckets_x27_327_);
lean_ctor_set(v___x_307_, 0, v_size_x27_325_);
v___x_339_ = v___x_307_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_size_x27_325_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_buckets_x27_327_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
else
{
lean_object* v___x_341_; lean_object* v_buckets_x27_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
lean_inc(v_bkt_322_);
v___x_341_ = lean_box(0);
v_buckets_x27_342_ = lean_array_uset(v_buckets_305_, v___x_321_, v___x_341_);
v___x_343_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_302_, v_b_303_, v_bkt_322_);
v___x_344_ = lean_array_uset(v_buckets_x27_342_, v___x_321_, v___x_343_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_344_);
v___x_346_ = v___x_307_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_size_304_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object* v_a_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v___x_351_; 
v___x_351_ = lean_box(0);
return v___x_351_;
}
else
{
lean_object* v_key_352_; lean_object* v_value_353_; lean_object* v_tail_354_; uint8_t v___x_355_; 
v_key_352_ = lean_ctor_get(v_x_350_, 0);
v_value_353_ = lean_ctor_get(v_x_350_, 1);
v_tail_354_ = lean_ctor_get(v_x_350_, 2);
v___x_355_ = lean_expr_eqv(v_key_352_, v_a_349_);
if (v___x_355_ == 0)
{
v_x_350_ = v_tail_354_;
goto _start;
}
else
{
lean_object* v___x_357_; 
lean_inc(v_value_353_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v_value_353_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_358_, v_x_359_);
lean_dec(v_x_359_);
lean_dec_ref(v_a_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object* v_m_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_buckets_363_; lean_object* v___x_364_; uint64_t v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v_fold_368_; uint64_t v___x_369_; uint64_t v___x_370_; uint64_t v___x_371_; size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; size_t v___x_375_; size_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_buckets_363_ = lean_ctor_get(v_m_361_, 1);
v___x_364_ = lean_array_get_size(v_buckets_363_);
v___x_365_ = l_Lean_Expr_hash(v_a_362_);
v___x_366_ = 32ULL;
v___x_367_ = lean_uint64_shift_right(v___x_365_, v___x_366_);
v_fold_368_ = lean_uint64_xor(v___x_365_, v___x_367_);
v___x_369_ = 16ULL;
v___x_370_ = lean_uint64_shift_right(v_fold_368_, v___x_369_);
v___x_371_ = lean_uint64_xor(v_fold_368_, v___x_370_);
v___x_372_ = lean_uint64_to_usize(v___x_371_);
v___x_373_ = lean_usize_of_nat(v___x_364_);
v___x_374_ = ((size_t)1ULL);
v___x_375_ = lean_usize_sub(v___x_373_, v___x_374_);
v___x_376_ = lean_usize_land(v___x_372_, v___x_375_);
v___x_377_ = lean_array_uget_borrowed(v_buckets_363_, v___x_376_);
v___x_378_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_362_, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object* v_m_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_379_, v_a_380_);
lean_dec_ref(v_a_380_);
lean_dec_ref(v_m_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(lean_object* v_e_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_op_385_; lean_object* v_exprToVarIndex_386_; lean_object* v_varToExpr_387_; lean_object* v___x_388_; 
v_op_385_ = lean_ctor_get(v_a_383_, 0);
v_exprToVarIndex_386_ = lean_ctor_get(v_a_383_, 1);
v_varToExpr_387_ = lean_ctor_get(v_a_383_, 2);
v___x_388_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_exprToVarIndex_386_, v_e_382_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_400_; 
lean_inc_ref(v_varToExpr_387_);
lean_inc_ref(v_exprToVarIndex_386_);
lean_inc_ref(v_op_385_);
v_isSharedCheck_400_ = !lean_is_exclusive(v_a_383_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; lean_object* v_unused_402_; lean_object* v_unused_403_; 
v_unused_401_ = lean_ctor_get(v_a_383_, 2);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_a_383_, 1);
lean_dec(v_unused_402_);
v_unused_403_ = lean_ctor_get(v_a_383_, 0);
lean_dec(v_unused_403_);
v___x_390_ = v_a_383_;
v_isShared_391_ = v_isSharedCheck_400_;
goto v_resetjp_389_;
}
else
{
lean_dec(v_a_383_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_400_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v_size_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v_size_392_ = lean_ctor_get(v_exprToVarIndex_386_, 0);
lean_inc_n(v_size_392_, 2);
lean_inc_ref(v_e_382_);
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_exprToVarIndex_386_, v_e_382_, v_size_392_);
v___x_394_ = lean_array_push(v_varToExpr_387_, v_e_382_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 2, v___x_394_);
lean_ctor_set(v___x_390_, 1, v___x_393_);
v___x_396_ = v___x_390_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_op_385_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v___x_394_);
v___x_396_ = v_reuseFailAlloc_399_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_size_392_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
}
else
{
lean_object* v_val_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v_e_382_);
v_val_404_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_388_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_val_404_);
lean_dec(v___x_388_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_val_404_);
lean_ctor_set(v___x_408_, 1, v_a_383_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 0);
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object* v_e_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_413_, v_a_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(lean_object* v_e_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_417_, v_a_418_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___boxed(lean_object* v_e_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(v_e_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(lean_object* v_00_u03b2_437_, lean_object* v_m_438_, lean_object* v_a_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_438_, v_a_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object* v_00_u03b2_441_, lean_object* v_m_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(v_00_u03b2_441_, v_m_442_, v_a_443_);
lean_dec_ref(v_a_443_);
lean_dec_ref(v_m_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1(lean_object* v_00_u03b2_445_, lean_object* v_m_446_, lean_object* v_a_447_, lean_object* v_b_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_m_446_, v_a_447_, v_b_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object* v_00_u03b2_450_, lean_object* v_a_451_, lean_object* v_x_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_451_, v_x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_454_, lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(v_00_u03b2_454_, v_a_455_, v_x_456_);
lean_dec(v_x_456_);
lean_dec_ref(v_a_455_);
return v_res_457_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object* v_00_u03b2_458_, lean_object* v_a_459_, lean_object* v_x_460_){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_459_, v_x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_462_, lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(v_00_u03b2_462_, v_a_463_, v_x_464_);
lean_dec(v_x_464_);
lean_dec_ref(v_a_463_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3(lean_object* v_00_u03b2_467_, lean_object* v_data_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_data_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4(lean_object* v_00_u03b2_470_, lean_object* v_a_471_, lean_object* v_b_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_471_, v_b_472_, v_x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_475_, lean_object* v_i_476_, lean_object* v_source_477_, lean_object* v_target_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v_i_476_, v_source_477_, v_target_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_481_, v_x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object* v_msgData_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; lean_object* v_env_491_; lean_object* v___x_492_; lean_object* v_mctx_493_; lean_object* v_lctx_494_; lean_object* v_options_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_490_ = lean_st_ref_get(v___y_488_);
v_env_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc_ref(v_env_491_);
lean_dec(v___x_490_);
v___x_492_ = lean_st_ref_get(v___y_486_);
v_mctx_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc_ref(v_mctx_493_);
lean_dec(v___x_492_);
v_lctx_494_ = lean_ctor_get(v___y_485_, 2);
v_options_495_ = lean_ctor_get(v___y_487_, 2);
lean_inc_ref(v_options_495_);
lean_inc_ref(v_lctx_494_);
v___x_496_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_496_, 0, v_env_491_);
lean_ctor_set(v___x_496_, 1, v_mctx_493_);
lean_ctor_set(v___x_496_, 2, v_lctx_494_);
lean_ctor_set(v___x_496_, 3, v_options_495_);
v___x_497_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v_msgData_484_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object* v_msgData_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msgData_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object* v_msg_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_ref_512_; lean_object* v___x_513_; lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
v_ref_512_ = lean_ctor_get(v___y_509_, 5);
v___x_513_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_522_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
lean_inc(v_ref_512_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_ref_512_);
lean_ctor_set(v___x_518_, 1, v_a_514_);
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 1);
lean_ctor_set(v___x_516_, 0, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object* v_msg_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
if (lean_obj_tag(v_a_530_) == 0)
{
lean_object* v___x_532_; 
v___x_532_ = l_List_reverse___redArg(v_a_531_);
return v___x_532_;
}
else
{
lean_object* v_head_533_; lean_object* v_tail_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_543_; 
v_head_533_ = lean_ctor_get(v_a_530_, 0);
v_tail_534_ = lean_ctor_get(v_a_530_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_a_530_);
if (v_isSharedCheck_543_ == 0)
{
v___x_536_ = v_a_530_;
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_tail_534_);
lean_inc(v_head_533_);
lean_dec(v_a_530_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = l_Lean_MessageData_ofExpr(v_head_533_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v_a_531_);
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_a_531_);
v___x_540_ = v_reuseFailAlloc_542_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
v_a_530_ = v_tail_534_;
v_a_531_ = v___x_540_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0));
v___x_546_ = l_Lean_stringToMessageData(v___x_545_);
return v___x_546_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2));
v___x_549_ = l_Lean_stringToMessageData(v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4));
v___x_552_ = l_Lean_stringToMessageData(v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(lean_object* v_idx_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_varToExpr_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_varToExpr_562_ = lean_ctor_get(v_a_554_, 2);
v___x_563_ = lean_array_get_size(v_varToExpr_562_);
v___x_564_ = lean_nat_dec_lt(v_idx_553_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_inc_ref(v_varToExpr_562_);
lean_dec_ref(v_a_554_);
v___x_565_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1);
v___x_566_ = l_Nat_reprFast(v_idx_553_);
v___x_567_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
v___x_568_ = l_Lean_MessageData_ofFormat(v___x_567_);
v___x_569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_565_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3);
v___x_571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Nat_reprFast(v___x_563_);
v___x_573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
v___x_574_ = l_Lean_MessageData_ofFormat(v___x_573_);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_571_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_array_to_list(v_varToExpr_562_);
v___x_579_ = lean_box(0);
v___x_580_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(v___x_578_, v___x_579_);
v___x_581_ = l_Lean_MessageData_ofList(v___x_580_);
v___x_582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_577_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v___x_582_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_array_fget(v_varToExpr_562_, v_idx_553_);
lean_dec(v_idx_553_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v_a_554_);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___boxed(lean_object* v_idx_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(v_idx_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_object* v_00_u03b1_597_, lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_598_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object* v_00_u03b1_608_, lean_object* v_msg_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(v_00_u03b1_608_, v_msg_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object* v_c_619_){
_start:
{
lean_object* v___y_621_; 
if (lean_obj_tag(v_c_619_) == 0)
{
lean_object* v___x_625_; 
v___x_625_ = lean_unsigned_to_nat(0u);
v___y_621_ = v___x_625_;
goto v___jp_620_;
}
else
{
lean_object* v_val_626_; 
v_val_626_ = lean_ctor_get(v_c_619_, 0);
v___y_621_ = v_val_626_;
goto v___jp_620_;
}
v___jp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = lean_nat_add(v___y_621_, v___x_622_);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object* v_c_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v_c_627_);
lean_dec(v_c_627_);
return v_res_628_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_box(0);
v___x_630_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object* v_a_631_, lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_object* v___x_633_; lean_object* v_val_634_; lean_object* v___x_635_; 
v___x_633_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0);
v_val_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_val_634_);
v___x_635_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_635_, 0, v_a_631_);
lean_ctor_set(v___x_635_, 1, v_val_634_);
lean_ctor_set(v___x_635_, 2, v_x_632_);
return v___x_635_;
}
else
{
lean_object* v_key_636_; lean_object* v_value_637_; lean_object* v_tail_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_653_; 
v_key_636_ = lean_ctor_get(v_x_632_, 0);
v_value_637_ = lean_ctor_get(v_x_632_, 1);
v_tail_638_ = lean_ctor_get(v_x_632_, 2);
v_isSharedCheck_653_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_653_ == 0)
{
v___x_640_ = v_x_632_;
v_isShared_641_ = v_isSharedCheck_653_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_tail_638_);
lean_inc(v_value_637_);
lean_inc(v_key_636_);
lean_dec(v_x_632_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_653_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
uint8_t v___x_642_; 
v___x_642_ = lean_nat_dec_eq(v_key_636_, v_a_631_);
if (v___x_642_ == 0)
{
lean_object* v_tail_643_; lean_object* v___x_645_; 
v_tail_643_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_631_, v_tail_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 2, v_tail_643_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_key_636_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_value_637_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_tail_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_val_649_; lean_object* v___x_651_; 
lean_dec(v_key_636_);
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v_value_637_);
v___x_648_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_647_);
lean_dec_ref_known(v___x_647_, 1);
v_val_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_649_);
lean_dec(v___x_648_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_val_649_);
lean_ctor_set(v___x_640_, 0, v_a_631_);
v___x_651_ = v___x_640_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_631_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_val_649_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_tail_638_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
if (lean_obj_tag(v_x_655_) == 0)
{
return v_x_654_;
}
else
{
lean_object* v_key_656_; lean_object* v_value_657_; lean_object* v_tail_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_681_; 
v_key_656_ = lean_ctor_get(v_x_655_, 0);
v_value_657_ = lean_ctor_get(v_x_655_, 1);
v_tail_658_ = lean_ctor_get(v_x_655_, 2);
v_isSharedCheck_681_ = !lean_is_exclusive(v_x_655_);
if (v_isSharedCheck_681_ == 0)
{
v___x_660_ = v_x_655_;
v_isShared_661_ = v_isSharedCheck_681_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_tail_658_);
lean_inc(v_value_657_);
lean_inc(v_key_656_);
lean_dec(v_x_655_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_681_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; uint64_t v___x_663_; uint64_t v___x_664_; uint64_t v___x_665_; uint64_t v_fold_666_; uint64_t v___x_667_; uint64_t v___x_668_; uint64_t v___x_669_; size_t v___x_670_; size_t v___x_671_; size_t v___x_672_; size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_662_ = lean_array_get_size(v_x_654_);
v___x_663_ = lean_uint64_of_nat(v_key_656_);
v___x_664_ = 32ULL;
v___x_665_ = lean_uint64_shift_right(v___x_663_, v___x_664_);
v_fold_666_ = lean_uint64_xor(v___x_663_, v___x_665_);
v___x_667_ = 16ULL;
v___x_668_ = lean_uint64_shift_right(v_fold_666_, v___x_667_);
v___x_669_ = lean_uint64_xor(v_fold_666_, v___x_668_);
v___x_670_ = lean_uint64_to_usize(v___x_669_);
v___x_671_ = lean_usize_of_nat(v___x_662_);
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_sub(v___x_671_, v___x_672_);
v___x_674_ = lean_usize_land(v___x_670_, v___x_673_);
v___x_675_ = lean_array_uget_borrowed(v_x_654_, v___x_674_);
lean_inc(v___x_675_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 2, v___x_675_);
v___x_677_ = v___x_660_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_key_656_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_value_657_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v___x_675_);
v___x_677_ = v_reuseFailAlloc_680_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; 
v___x_678_ = lean_array_uset(v_x_654_, v___x_674_, v___x_677_);
v_x_654_ = v___x_678_;
v_x_655_ = v_tail_658_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_682_, lean_object* v_source_683_, lean_object* v_target_684_){
_start:
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_array_get_size(v_source_683_);
v___x_686_ = lean_nat_dec_lt(v_i_682_, v___x_685_);
if (v___x_686_ == 0)
{
lean_dec_ref(v_source_683_);
lean_dec(v_i_682_);
return v_target_684_;
}
else
{
lean_object* v_es_687_; lean_object* v___x_688_; lean_object* v_source_689_; lean_object* v_target_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_es_687_ = lean_array_fget(v_source_683_, v_i_682_);
v___x_688_ = lean_box(0);
v_source_689_ = lean_array_fset(v_source_683_, v_i_682_, v___x_688_);
v_target_690_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_684_, v_es_687_);
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_nat_add(v_i_682_, v___x_691_);
lean_dec(v_i_682_);
v_i_682_ = v___x_692_;
v_source_683_ = v_source_689_;
v_target_684_ = v_target_690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object* v_data_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v_nbuckets_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_695_ = lean_array_get_size(v_data_694_);
v___x_696_ = lean_unsigned_to_nat(2u);
v_nbuckets_697_ = lean_nat_mul(v___x_695_, v___x_696_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_box(0);
v___x_700_ = lean_mk_array(v_nbuckets_697_, v___x_699_);
v___x_701_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v___x_698_, v_data_694_, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object* v_a_702_, lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
uint8_t v___x_704_; 
v___x_704_ = 0;
return v___x_704_;
}
else
{
lean_object* v_key_705_; lean_object* v_tail_706_; uint8_t v___x_707_; 
v_key_705_ = lean_ctor_get(v_x_703_, 0);
v_tail_706_ = lean_ctor_get(v_x_703_, 2);
v___x_707_ = lean_nat_dec_eq(v_key_705_, v_a_702_);
if (v___x_707_ == 0)
{
v_x_703_ = v_tail_706_;
goto _start;
}
else
{
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_709_, lean_object* v_x_710_){
_start:
{
uint8_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_709_, v_x_710_);
lean_dec(v_x_710_);
lean_dec(v_a_709_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object* v_m_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_size_715_; lean_object* v_buckets_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_764_; 
v_size_715_ = lean_ctor_get(v_m_713_, 0);
v_buckets_716_ = lean_ctor_get(v_m_713_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_m_713_);
if (v_isSharedCheck_764_ == 0)
{
v___x_718_ = v_m_713_;
v_isShared_719_ = v_isSharedCheck_764_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_buckets_716_);
lean_inc(v_size_715_);
lean_dec(v_m_713_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_764_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; uint64_t v___x_721_; uint64_t v___x_722_; uint64_t v___x_723_; uint64_t v_fold_724_; uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; size_t v___x_728_; size_t v___x_729_; size_t v___x_730_; size_t v___x_731_; size_t v___x_732_; lean_object* v_bkt_733_; uint8_t v___x_734_; 
v___x_720_ = lean_array_get_size(v_buckets_716_);
v___x_721_ = lean_uint64_of_nat(v_a_714_);
v___x_722_ = 32ULL;
v___x_723_ = lean_uint64_shift_right(v___x_721_, v___x_722_);
v_fold_724_ = lean_uint64_xor(v___x_721_, v___x_723_);
v___x_725_ = 16ULL;
v___x_726_ = lean_uint64_shift_right(v_fold_724_, v___x_725_);
v___x_727_ = lean_uint64_xor(v_fold_724_, v___x_726_);
v___x_728_ = lean_uint64_to_usize(v___x_727_);
v___x_729_ = lean_usize_of_nat(v___x_720_);
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_sub(v___x_729_, v___x_730_);
v___x_732_ = lean_usize_land(v___x_728_, v___x_731_);
v_bkt_733_ = lean_array_uget_borrowed(v_buckets_716_, v___x_732_);
v___x_734_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_714_, v_bkt_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v_size_x27_736_; lean_object* v___x_737_; lean_object* v_buckets_x27_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_735_ = lean_unsigned_to_nat(1u);
v_size_x27_736_ = lean_nat_add(v_size_715_, v___x_735_);
lean_dec(v_size_715_);
lean_inc(v_bkt_733_);
v___x_737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_737_, 0, v_a_714_);
lean_ctor_set(v___x_737_, 1, v___x_735_);
lean_ctor_set(v___x_737_, 2, v_bkt_733_);
v_buckets_x27_738_ = lean_array_uset(v_buckets_716_, v___x_732_, v___x_737_);
v___x_739_ = lean_unsigned_to_nat(4u);
v___x_740_ = lean_nat_mul(v_size_x27_736_, v___x_739_);
v___x_741_ = lean_unsigned_to_nat(3u);
v___x_742_ = lean_nat_div(v___x_740_, v___x_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_array_get_size(v_buckets_x27_738_);
v___x_744_ = lean_nat_dec_le(v___x_742_, v___x_743_);
lean_dec(v___x_742_);
if (v___x_744_ == 0)
{
lean_object* v_val_745_; lean_object* v___x_747_; 
v_val_745_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_738_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v_val_745_);
lean_ctor_set(v___x_718_, 0, v_size_x27_736_);
v___x_747_ = v___x_718_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_size_x27_736_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_val_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
else
{
lean_object* v___x_750_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v_buckets_x27_738_);
lean_ctor_set(v___x_718_, 0, v_size_x27_736_);
v___x_750_ = v___x_718_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_size_x27_736_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_buckets_x27_738_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
else
{
lean_object* v___x_752_; lean_object* v_buckets_x27_753_; lean_object* v_bkt_x27_754_; lean_object* v___y_756_; uint8_t v___x_761_; 
lean_inc(v_bkt_733_);
v___x_752_ = lean_box(0);
v_buckets_x27_753_ = lean_array_uset(v_buckets_716_, v___x_732_, v___x_752_);
lean_inc(v_a_714_);
v_bkt_x27_754_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_714_, v_bkt_733_);
v___x_761_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_714_, v_bkt_x27_754_);
lean_dec(v_a_714_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_sub(v_size_715_, v___x_762_);
lean_dec(v_size_715_);
v___y_756_ = v___x_763_;
goto v___jp_755_;
}
else
{
v___y_756_ = v_size_715_;
goto v___jp_755_;
}
v___jp_755_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_array_uset(v_buckets_x27_753_, v___x_732_, v_bkt_x27_754_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_757_);
lean_ctor_set(v___x_718_, 0, v___y_756_);
v___x_759_ = v___x_718_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___y_756_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object* v_coeff_765_, lean_object* v_e_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_769_; lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_787_; 
v___x_769_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_766_, v_a_767_);
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_787_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_787_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_787_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_fst_774_; lean_object* v_snd_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_786_; 
v_fst_774_ = lean_ctor_get(v_a_770_, 0);
v_snd_775_ = lean_ctor_get(v_a_770_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v_a_770_);
if (v_isSharedCheck_786_ == 0)
{
v___x_777_ = v_a_770_;
v_isShared_778_ = v_isSharedCheck_786_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_snd_775_);
lean_inc(v_fst_774_);
lean_dec(v_a_770_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_786_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(v_coeff_765_, v_fst_774_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_779_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_snd_775_);
v___x_781_ = v_reuseFailAlloc_785_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_781_);
v___x_783_ = v___x_772_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object* v_coeff_788_, lean_object* v_e_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_788_, v_e_789_, v_a_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object* v_coeff_793_, lean_object* v_e_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_793_, v_e_794_, v_a_795_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object* v_coeff_804_, lean_object* v_e_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(v_coeff_804_, v_e_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
return v_res_814_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object* v_00_u03b2_815_, lean_object* v_a_816_, lean_object* v_x_817_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_816_, v_x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_819_, lean_object* v_a_820_, lean_object* v_x_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(v_00_u03b2_819_, v_a_820_, v_x_821_);
lean_dec(v_x_821_);
lean_dec(v_a_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object* v_00_u03b2_824_, lean_object* v_data_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_data_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_827_, lean_object* v_i_828_, lean_object* v_source_829_, lean_object* v_target_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v_i_828_, v_source_829_, v_target_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_832_, lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_833_, v_x_834_);
return v___x_835_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_836_; double v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_float_of_nat(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(lean_object* v_cls_841_, lean_object* v_msg_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_ref_849_; lean_object* v___x_850_; lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_896_; 
v_ref_849_ = lean_ctor_get(v___y_846_, 5);
v___x_850_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_842_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_896_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_896_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_896_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v_traceState_856_; lean_object* v_env_857_; lean_object* v_nextMacroScope_858_; lean_object* v_ngen_859_; lean_object* v_auxDeclNGen_860_; lean_object* v_cache_861_; lean_object* v_messages_862_; lean_object* v_infoState_863_; lean_object* v_snapshotTasks_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_895_; 
v___x_855_ = lean_st_ref_take(v___y_847_);
v_traceState_856_ = lean_ctor_get(v___x_855_, 4);
v_env_857_ = lean_ctor_get(v___x_855_, 0);
v_nextMacroScope_858_ = lean_ctor_get(v___x_855_, 1);
v_ngen_859_ = lean_ctor_get(v___x_855_, 2);
v_auxDeclNGen_860_ = lean_ctor_get(v___x_855_, 3);
v_cache_861_ = lean_ctor_get(v___x_855_, 5);
v_messages_862_ = lean_ctor_get(v___x_855_, 6);
v_infoState_863_ = lean_ctor_get(v___x_855_, 7);
v_snapshotTasks_864_ = lean_ctor_get(v___x_855_, 8);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_895_ == 0)
{
v___x_866_ = v___x_855_;
v_isShared_867_ = v_isSharedCheck_895_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snapshotTasks_864_);
lean_inc(v_infoState_863_);
lean_inc(v_messages_862_);
lean_inc(v_cache_861_);
lean_inc(v_traceState_856_);
lean_inc(v_auxDeclNGen_860_);
lean_inc(v_ngen_859_);
lean_inc(v_nextMacroScope_858_);
lean_inc(v_env_857_);
lean_dec(v___x_855_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_895_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint64_t v_tid_868_; lean_object* v_traces_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_894_; 
v_tid_868_ = lean_ctor_get_uint64(v_traceState_856_, sizeof(void*)*1);
v_traces_869_ = lean_ctor_get(v_traceState_856_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v_traceState_856_);
if (v_isSharedCheck_894_ == 0)
{
v___x_871_ = v_traceState_856_;
v_isShared_872_ = v_isSharedCheck_894_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_traces_869_);
lean_dec(v_traceState_856_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_894_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; double v___x_874_; uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_873_ = lean_box(0);
v___x_874_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_875_ = 0;
v___x_876_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_877_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_877_, 0, v_cls_841_);
lean_ctor_set(v___x_877_, 1, v___x_873_);
lean_ctor_set(v___x_877_, 2, v___x_876_);
lean_ctor_set_float(v___x_877_, sizeof(void*)*3, v___x_874_);
lean_ctor_set_float(v___x_877_, sizeof(void*)*3 + 8, v___x_874_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*3 + 16, v___x_875_);
v___x_878_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_879_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v_a_851_);
lean_ctor_set(v___x_879_, 2, v___x_878_);
lean_inc(v_ref_849_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_ref_849_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Lean_PersistentArray_push___redArg(v_traces_869_, v___x_880_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_881_);
v___x_883_ = v___x_871_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_881_);
lean_ctor_set_uint64(v_reuseFailAlloc_893_, sizeof(void*)*1, v_tid_868_);
v___x_883_ = v_reuseFailAlloc_893_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 4, v___x_883_);
v___x_885_ = v___x_866_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_env_857_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_nextMacroScope_858_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_ngen_859_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_auxDeclNGen_860_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_892_, 5, v_cache_861_);
lean_ctor_set(v_reuseFailAlloc_892_, 6, v_messages_862_);
lean_ctor_set(v_reuseFailAlloc_892_, 7, v_infoState_863_);
lean_ctor_set(v_reuseFailAlloc_892_, 8, v_snapshotTasks_864_);
v___x_885_ = v_reuseFailAlloc_892_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_886_ = lean_st_ref_set(v___y_847_, v___x_885_);
v___x_887_ = lean_box(0);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___y_843_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_888_);
v___x_890_ = v___x_853_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___boxed(lean_object* v_cls_897_, lean_object* v_msg_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_897_, v_msg_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_905_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6(void){
_start:
{
lean_object* v_cls_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_cls_916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_918_ = l_Lean_Name_append(v___x_917_, v_cls_916_);
return v___x_918_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7));
v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9));
v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11));
v___x_927_ = l_Lean_stringToMessageData(v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13));
v___x_930_ = l_Lean_stringToMessageData(v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_931_, lean_object* v_coeff_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
if (lean_obj_tag(v_a_933_) == 5)
{
lean_object* v_fn_942_; 
v_fn_942_ = lean_ctor_get(v_a_933_, 0);
if (lean_obj_tag(v_fn_942_) == 5)
{
lean_object* v_arg_943_; lean_object* v_fn_944_; lean_object* v_arg_945_; uint8_t v___x_946_; 
v_arg_943_ = lean_ctor_get(v_a_933_, 1);
v_fn_944_ = lean_ctor_get(v_fn_942_, 0);
v_arg_945_ = lean_ctor_get(v_fn_942_, 1);
lean_inc_ref(v_fn_944_);
v___x_946_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_fn_944_);
if (v___x_946_ == 0)
{
lean_object* v_options_947_; uint8_t v_hasTrace_948_; 
v_options_947_ = lean_ctor_get(v_a_939_, 2);
v_hasTrace_948_ = lean_ctor_get_uint8(v_options_947_, sizeof(void*)*1);
if (v_hasTrace_948_ == 0)
{
lean_object* v___x_949_; 
lean_dec_ref(v_op_931_);
v___x_949_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_a_934_);
return v___x_949_;
}
else
{
lean_object* v_inheritedTraceOptions_950_; lean_object* v_cls_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_inheritedTraceOptions_950_ = lean_ctor_get(v_a_939_, 13);
v_cls_951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_952_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_953_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_950_, v_options_947_, v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
lean_dec_ref(v_op_931_);
v___x_954_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_a_934_);
return v___x_954_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_955_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_944_);
v___x_956_ = l_Lean_MessageData_ofExpr(v_fn_944_);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10);
v___x_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
lean_inc_ref(v_arg_945_);
v___x_960_ = l_Lean_MessageData_ofExpr(v_arg_945_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v___x_958_);
lean_inc_ref(v_arg_943_);
v___x_963_ = l_Lean_MessageData_ofExpr(v_arg_943_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_931_);
v___x_968_ = l_Lean_MessageData_ofExpr(v___x_967_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_966_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_951_, v___x_971_, v_a_934_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v_snd_974_; lean_object* v___x_975_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_972_, 1);
v_snd_974_ = lean_ctor_get(v_a_973_, 1);
lean_inc(v_snd_974_);
lean_dec(v_a_973_);
v___x_975_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_snd_974_);
return v___x_975_;
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref_known(v_a_933_, 2);
lean_dec_ref(v_coeff_932_);
v_a_976_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_972_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_972_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
}
else
{
lean_object* v___x_984_; 
lean_inc_ref(v_arg_945_);
lean_inc_ref(v_arg_943_);
lean_dec_ref_known(v_a_933_, 2);
lean_inc_ref(v_op_931_);
v___x_984_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_931_, v_coeff_932_, v_arg_945_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v_fst_986_; lean_object* v_snd_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
v_fst_986_ = lean_ctor_get(v_a_985_, 0);
lean_inc(v_fst_986_);
v_snd_987_ = lean_ctor_get(v_a_985_, 1);
lean_inc(v_snd_987_);
lean_dec(v_a_985_);
v_coeff_932_ = v_fst_986_;
v_a_933_ = v_arg_943_;
v_a_934_ = v_snd_987_;
goto _start;
}
else
{
lean_dec_ref(v_arg_943_);
lean_dec_ref(v_op_931_);
return v___x_984_;
}
}
}
else
{
lean_object* v___x_989_; 
lean_dec_ref(v_op_931_);
v___x_989_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_a_934_);
return v___x_989_;
}
}
else
{
lean_object* v___x_990_; 
lean_dec_ref(v_op_931_);
v___x_990_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_932_, v_a_933_, v_a_934_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_991_, lean_object* v_coeff_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_991_, v_coeff_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_1003_, lean_object* v_msg_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_1003_, v_msg_1004_, v___y_1005_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_1014_, lean_object* v_msg_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_1014_, v_msg_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
return v_res_1024_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_unsigned_to_nat(16u);
v___x_1027_ = lean_mk_array(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object* v_op_1031_, lean_object* v_e_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1042_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1031_, v___x_1041_, v_e_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_1043_, lean_object* v_e_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_op_1043_, v_e_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1054_, lean_object* v_x_1055_){
_start:
{
if (lean_obj_tag(v_x_1055_) == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_box(0);
return v___x_1056_;
}
else
{
lean_object* v_key_1057_; lean_object* v_value_1058_; lean_object* v_tail_1059_; uint8_t v___x_1060_; 
v_key_1057_ = lean_ctor_get(v_x_1055_, 0);
v_value_1058_ = lean_ctor_get(v_x_1055_, 1);
v_tail_1059_ = lean_ctor_get(v_x_1055_, 2);
v___x_1060_ = lean_nat_dec_eq(v_key_1057_, v_a_1054_);
if (v___x_1060_ == 0)
{
v_x_1055_ = v_tail_1059_;
goto _start;
}
else
{
lean_object* v___x_1062_; 
lean_inc(v_value_1058_);
v___x_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_value_1058_);
return v___x_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1063_, v_x_1064_);
lean_dec(v_x_1064_);
lean_dec(v_a_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_buckets_1068_; lean_object* v___x_1069_; uint64_t v___x_1070_; uint64_t v___x_1071_; uint64_t v___x_1072_; uint64_t v_fold_1073_; uint64_t v___x_1074_; uint64_t v___x_1075_; uint64_t v___x_1076_; size_t v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_buckets_1068_ = lean_ctor_get(v_m_1066_, 1);
v___x_1069_ = lean_array_get_size(v_buckets_1068_);
v___x_1070_ = lean_uint64_of_nat(v_a_1067_);
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
v___x_1082_ = lean_array_uget_borrowed(v_buckets_1068_, v___x_1081_);
v___x_1083_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1067_, v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_m_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1087_, lean_object* v_b_1088_, lean_object* v_x_1089_){
_start:
{
if (lean_obj_tag(v_x_1089_) == 0)
{
lean_dec(v_b_1088_);
lean_dec(v_a_1087_);
return v_x_1089_;
}
else
{
lean_object* v_key_1090_; lean_object* v_value_1091_; lean_object* v_tail_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1104_; 
v_key_1090_ = lean_ctor_get(v_x_1089_, 0);
v_value_1091_ = lean_ctor_get(v_x_1089_, 1);
v_tail_1092_ = lean_ctor_get(v_x_1089_, 2);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_x_1089_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1094_ = v_x_1089_;
v_isShared_1095_ = v_isSharedCheck_1104_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_tail_1092_);
lean_inc(v_value_1091_);
lean_inc(v_key_1090_);
lean_dec(v_x_1089_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1104_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_nat_dec_eq(v_key_1090_, v_a_1087_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1087_, v_b_1088_, v_tail_1092_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 2, v___x_1097_);
v___x_1099_ = v___x_1094_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_key_1090_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_value_1091_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
else
{
lean_object* v___x_1102_; 
lean_dec(v_value_1091_);
lean_dec(v_key_1090_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v_b_1088_);
lean_ctor_set(v___x_1094_, 0, v_a_1087_);
v___x_1102_ = v___x_1094_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1087_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_b_1088_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_tail_1092_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1105_, lean_object* v_a_1106_, lean_object* v_b_1107_){
_start:
{
lean_object* v_size_1108_; lean_object* v_buckets_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1152_; 
v_size_1108_ = lean_ctor_get(v_m_1105_, 0);
v_buckets_1109_ = lean_ctor_get(v_m_1105_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_m_1105_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1111_ = v_m_1105_;
v_isShared_1112_ = v_isSharedCheck_1152_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_buckets_1109_);
lean_inc(v_size_1108_);
lean_dec(v_m_1105_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1152_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; uint64_t v___x_1114_; uint64_t v___x_1115_; uint64_t v___x_1116_; uint64_t v_fold_1117_; uint64_t v___x_1118_; uint64_t v___x_1119_; uint64_t v___x_1120_; size_t v___x_1121_; size_t v___x_1122_; size_t v___x_1123_; size_t v___x_1124_; size_t v___x_1125_; lean_object* v_bkt_1126_; uint8_t v___x_1127_; 
v___x_1113_ = lean_array_get_size(v_buckets_1109_);
v___x_1114_ = lean_uint64_of_nat(v_a_1106_);
v___x_1115_ = 32ULL;
v___x_1116_ = lean_uint64_shift_right(v___x_1114_, v___x_1115_);
v_fold_1117_ = lean_uint64_xor(v___x_1114_, v___x_1116_);
v___x_1118_ = 16ULL;
v___x_1119_ = lean_uint64_shift_right(v_fold_1117_, v___x_1118_);
v___x_1120_ = lean_uint64_xor(v_fold_1117_, v___x_1119_);
v___x_1121_ = lean_uint64_to_usize(v___x_1120_);
v___x_1122_ = lean_usize_of_nat(v___x_1113_);
v___x_1123_ = ((size_t)1ULL);
v___x_1124_ = lean_usize_sub(v___x_1122_, v___x_1123_);
v___x_1125_ = lean_usize_land(v___x_1121_, v___x_1124_);
v_bkt_1126_ = lean_array_uget_borrowed(v_buckets_1109_, v___x_1125_);
v___x_1127_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1106_, v_bkt_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v_size_x27_1129_; lean_object* v___x_1130_; lean_object* v_buckets_x27_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1128_ = lean_unsigned_to_nat(1u);
v_size_x27_1129_ = lean_nat_add(v_size_1108_, v___x_1128_);
lean_dec(v_size_1108_);
lean_inc(v_bkt_1126_);
v___x_1130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1130_, 0, v_a_1106_);
lean_ctor_set(v___x_1130_, 1, v_b_1107_);
lean_ctor_set(v___x_1130_, 2, v_bkt_1126_);
v_buckets_x27_1131_ = lean_array_uset(v_buckets_1109_, v___x_1125_, v___x_1130_);
v___x_1132_ = lean_unsigned_to_nat(4u);
v___x_1133_ = lean_nat_mul(v_size_x27_1129_, v___x_1132_);
v___x_1134_ = lean_unsigned_to_nat(3u);
v___x_1135_ = lean_nat_div(v___x_1133_, v___x_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_array_get_size(v_buckets_x27_1131_);
v___x_1137_ = lean_nat_dec_le(v___x_1135_, v___x_1136_);
lean_dec(v___x_1135_);
if (v___x_1137_ == 0)
{
lean_object* v_val_1138_; lean_object* v___x_1140_; 
v_val_1138_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1131_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v_val_1138_);
lean_ctor_set(v___x_1111_, 0, v_size_x27_1129_);
v___x_1140_ = v___x_1111_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_size_x27_1129_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_val_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
else
{
lean_object* v___x_1143_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v_buckets_x27_1131_);
lean_ctor_set(v___x_1111_, 0, v_size_x27_1129_);
v___x_1143_ = v___x_1111_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_size_x27_1129_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_buckets_x27_1131_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v_buckets_x27_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
lean_inc(v_bkt_1126_);
v___x_1145_ = lean_box(0);
v_buckets_x27_1146_ = lean_array_uset(v_buckets_1109_, v___x_1125_, v___x_1145_);
v___x_1147_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1106_, v_b_1107_, v_bkt_1126_);
v___x_1148_ = lean_array_uset(v_buckets_x27_1146_, v___x_1125_, v___x_1147_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v___x_1148_);
v___x_1150_ = v___x_1111_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_size_1108_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
if (lean_obj_tag(v_x_1155_) == 0)
{
return v_x_1154_;
}
else
{
lean_object* v_key_1156_; lean_object* v_value_1157_; lean_object* v_tail_1158_; lean_object* v___y_1160_; lean_object* v___x_1163_; 
v_key_1156_ = lean_ctor_get(v_x_1155_, 0);
lean_inc(v_key_1156_);
v_value_1157_ = lean_ctor_get(v_x_1155_, 1);
lean_inc(v_value_1157_);
v_tail_1158_ = lean_ctor_get(v_x_1155_, 2);
lean_inc(v_tail_1158_);
lean_dec_ref_known(v_x_1155_, 3);
v___x_1163_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1153_, v_key_1156_);
if (lean_obj_tag(v___x_1163_) == 1)
{
lean_object* v_val_1164_; uint8_t v___x_1165_; 
v_val_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_val_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v___x_1165_ = lean_nat_dec_le(v_value_1157_, v_val_1164_);
if (v___x_1165_ == 0)
{
lean_dec(v_value_1157_);
v___y_1160_ = v_val_1164_;
goto v___jp_1159_;
}
else
{
lean_dec(v_val_1164_);
v___y_1160_ = v_value_1157_;
goto v___jp_1159_;
}
}
else
{
lean_dec(v___x_1163_);
lean_dec(v_value_1157_);
lean_dec(v_key_1156_);
v_x_1155_ = v_tail_1158_;
goto _start;
}
v___jp_1159_:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1154_, v_key_1156_, v___y_1160_);
v_x_1154_ = v___x_1161_;
v_x_1155_ = v_tail_1158_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1167_, lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1167_, v_x_1168_, v_x_1169_);
lean_dec_ref(v_snd_1167_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1171_, lean_object* v_as_1172_, size_t v_i_1173_, size_t v_stop_1174_, lean_object* v_b_1175_){
_start:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_eq(v_i_1173_, v_stop_1174_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; 
v___x_1177_ = lean_array_uget_borrowed(v_as_1172_, v_i_1173_);
lean_inc(v___x_1177_);
v___x_1178_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1171_, v_b_1175_, v___x_1177_);
v___x_1179_ = ((size_t)1ULL);
v___x_1180_ = lean_usize_add(v_i_1173_, v___x_1179_);
v_i_1173_ = v___x_1180_;
v_b_1175_ = v___x_1178_;
goto _start;
}
else
{
return v_b_1175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1182_, lean_object* v_as_1183_, lean_object* v_i_1184_, lean_object* v_stop_1185_, lean_object* v_b_1186_){
_start:
{
size_t v_i_boxed_1187_; size_t v_stop_boxed_1188_; lean_object* v_res_1189_; 
v_i_boxed_1187_ = lean_unbox_usize(v_i_1184_);
lean_dec(v_i_1184_);
v_stop_boxed_1188_ = lean_unbox_usize(v_stop_1185_);
lean_dec(v_stop_1185_);
v_res_1189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1182_, v_as_1183_, v_i_boxed_1187_, v_stop_boxed_1188_, v_b_1186_);
lean_dec_ref(v_as_1183_);
lean_dec_ref(v_snd_1182_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1190_, lean_object* v_a_1191_, lean_object* v_x_1192_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
lean_dec(v_a_1191_);
return v_x_1192_;
}
else
{
lean_object* v_key_1193_; lean_object* v_value_1194_; lean_object* v_tail_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1208_; 
v_key_1193_ = lean_ctor_get(v_x_1192_, 0);
v_value_1194_ = lean_ctor_get(v_x_1192_, 1);
v_tail_1195_ = lean_ctor_get(v_x_1192_, 2);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_x_1192_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1197_ = v_x_1192_;
v_isShared_1198_ = v_isSharedCheck_1208_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_tail_1195_);
lean_inc(v_value_1194_);
lean_inc(v_key_1193_);
lean_dec(v_x_1192_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1208_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
uint8_t v___x_1199_; 
v___x_1199_ = lean_nat_dec_eq(v_key_1193_, v_a_1191_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1200_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1190_, v_a_1191_, v_tail_1195_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 2, v___x_1200_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_key_1193_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_value_1194_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
lean_dec(v_key_1193_);
v___x_1204_ = lean_nat_sub(v_value_1194_, v_commonCnt_1190_);
lean_dec(v_value_1194_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 1, v___x_1204_);
lean_ctor_set(v___x_1197_, 0, v_a_1191_);
v___x_1206_ = v___x_1197_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1191_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_tail_1195_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1209_, lean_object* v_a_1210_, lean_object* v_x_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1209_, v_a_1210_, v_x_1211_);
lean_dec(v_commonCnt_1209_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1213_, lean_object* v_m_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_size_1216_; lean_object* v_buckets_1217_; lean_object* v___x_1218_; uint64_t v___x_1219_; uint64_t v___x_1220_; uint64_t v___x_1221_; uint64_t v_fold_1222_; uint64_t v___x_1223_; uint64_t v___x_1224_; uint64_t v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; lean_object* v_bucket_1231_; uint8_t v___x_1232_; 
v_size_1216_ = lean_ctor_get(v_m_1214_, 0);
v_buckets_1217_ = lean_ctor_get(v_m_1214_, 1);
v___x_1218_ = lean_array_get_size(v_buckets_1217_);
v___x_1219_ = lean_uint64_of_nat(v_a_1215_);
v___x_1220_ = 32ULL;
v___x_1221_ = lean_uint64_shift_right(v___x_1219_, v___x_1220_);
v_fold_1222_ = lean_uint64_xor(v___x_1219_, v___x_1221_);
v___x_1223_ = 16ULL;
v___x_1224_ = lean_uint64_shift_right(v_fold_1222_, v___x_1223_);
v___x_1225_ = lean_uint64_xor(v_fold_1222_, v___x_1224_);
v___x_1226_ = lean_uint64_to_usize(v___x_1225_);
v___x_1227_ = lean_usize_of_nat(v___x_1218_);
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_sub(v___x_1227_, v___x_1228_);
v___x_1230_ = lean_usize_land(v___x_1226_, v___x_1229_);
v_bucket_1231_ = lean_array_uget_borrowed(v_buckets_1217_, v___x_1230_);
v___x_1232_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1215_, v_bucket_1231_);
if (v___x_1232_ == 0)
{
lean_dec(v_a_1215_);
return v_m_1214_;
}
else
{
lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1243_; 
lean_inc(v_bucket_1231_);
lean_inc_ref(v_buckets_1217_);
lean_inc(v_size_1216_);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_m_1214_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; lean_object* v_unused_1245_; 
v_unused_1244_ = lean_ctor_get(v_m_1214_, 1);
lean_dec(v_unused_1244_);
v_unused_1245_ = lean_ctor_get(v_m_1214_, 0);
lean_dec(v_unused_1245_);
v___x_1234_ = v_m_1214_;
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
else
{
lean_dec(v_m_1214_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v_buckets_1237_; lean_object* v_bucket_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1236_ = lean_box(0);
v_buckets_1237_ = lean_array_uset(v_buckets_1217_, v___x_1230_, v___x_1236_);
v_bucket_1238_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1213_, v_a_1215_, v_bucket_1231_);
v___x_1239_ = lean_array_uset(v_buckets_1237_, v___x_1230_, v_bucket_1238_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 1, v___x_1239_);
v___x_1241_ = v___x_1234_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_size_1216_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1246_, lean_object* v_m_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1246_, v_m_1247_, v_a_1248_);
lean_dec(v_commonCnt_1246_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1250_, lean_object* v_x_1251_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
return v_x_1250_;
}
else
{
lean_object* v_key_1252_; lean_object* v_value_1253_; lean_object* v_tail_1254_; lean_object* v___x_1255_; 
v_key_1252_ = lean_ctor_get(v_x_1251_, 0);
lean_inc(v_key_1252_);
v_value_1253_ = lean_ctor_get(v_x_1251_, 1);
lean_inc(v_value_1253_);
v_tail_1254_ = lean_ctor_get(v_x_1251_, 2);
lean_inc(v_tail_1254_);
lean_dec_ref_known(v_x_1251_, 3);
v___x_1255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1253_, v_x_1250_, v_key_1252_);
lean_dec(v_value_1253_);
v_x_1250_ = v___x_1255_;
v_x_1251_ = v_tail_1254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
return v_x_1257_;
}
else
{
lean_object* v_key_1259_; lean_object* v_value_1260_; lean_object* v_tail_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_key_1259_ = lean_ctor_get(v_x_1258_, 0);
lean_inc(v_key_1259_);
v_value_1260_ = lean_ctor_get(v_x_1258_, 1);
lean_inc(v_value_1260_);
v_tail_1261_ = lean_ctor_get(v_x_1258_, 2);
lean_inc(v_tail_1261_);
lean_dec_ref_known(v_x_1258_, 3);
v___x_1262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1260_, v_x_1257_, v_key_1259_);
lean_dec(v_value_1260_);
v___x_1263_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1262_, v_tail_1261_);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1264_, size_t v_i_1265_, size_t v_stop_1266_, lean_object* v_b_1267_){
_start:
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_usize_dec_eq(v_i_1265_, v_stop_1266_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; 
v___x_1269_ = lean_array_uget_borrowed(v_as_1264_, v_i_1265_);
lean_inc(v___x_1269_);
v___x_1270_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(v_b_1267_, v___x_1269_);
v___x_1271_ = ((size_t)1ULL);
v___x_1272_ = lean_usize_add(v_i_1265_, v___x_1271_);
v_i_1265_ = v___x_1272_;
v_b_1267_ = v___x_1270_;
goto _start;
}
else
{
return v_b_1267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1274_, lean_object* v_i_1275_, lean_object* v_stop_1276_, lean_object* v_b_1277_){
_start:
{
size_t v_i_boxed_1278_; size_t v_stop_boxed_1279_; lean_object* v_res_1280_; 
v_i_boxed_1278_ = lean_unbox_usize(v_i_1275_);
lean_dec(v_i_1275_);
v_stop_boxed_1279_ = lean_unbox_usize(v_stop_1276_);
lean_dec(v_stop_1276_);
v_res_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_as_1274_, v_i_boxed_1278_, v_stop_boxed_1279_, v_b_1277_);
lean_dec_ref(v_as_1274_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1281_, lean_object* v_y_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v___y_1286_; lean_object* v_fst_1287_; lean_object* v_snd_1288_; lean_object* v_size_1292_; lean_object* v_buckets_1293_; lean_object* v_size_1294_; lean_object* v_buckets_1295_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1302_; lean_object* v_buckets_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v_buckets_1320_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v_fst_1337_; lean_object* v_buckets_1338_; lean_object* v_snd_1339_; uint8_t v___x_1352_; 
v_size_1292_ = lean_ctor_get(v_y_1282_, 0);
lean_inc(v_size_1292_);
v_buckets_1293_ = lean_ctor_get(v_y_1282_, 1);
v_size_1294_ = lean_ctor_get(v_x_1281_, 0);
lean_inc(v_size_1294_);
v_buckets_1295_ = lean_ctor_get(v_x_1281_, 1);
v___x_1352_ = lean_nat_dec_lt(v_size_1292_, v_size_1294_);
if (v___x_1352_ == 0)
{
lean_inc_ref(v_buckets_1295_);
v_fst_1337_ = v_x_1281_;
v_buckets_1338_ = v_buckets_1295_;
v_snd_1339_ = v_y_1282_;
goto v___jp_1336_;
}
else
{
lean_inc_ref(v_buckets_1293_);
v_fst_1337_ = v_y_1282_;
v_buckets_1338_ = v_buckets_1293_;
v_snd_1339_ = v_x_1281_;
goto v___jp_1336_;
}
v___jp_1285_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1289_, 0, v___y_1286_);
lean_ctor_set(v___x_1289_, 1, v_fst_1287_);
lean_ctor_set(v___x_1289_, 2, v_snd_1288_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v_a_1283_);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
v___jp_1296_:
{
uint8_t v___x_1300_; 
v___x_1300_ = lean_nat_dec_lt(v_size_1292_, v_size_1294_);
lean_dec(v_size_1294_);
lean_dec(v_size_1292_);
if (v___x_1300_ == 0)
{
v___y_1286_ = v___y_1297_;
v_fst_1287_ = v___y_1298_;
v_snd_1288_ = v___y_1299_;
goto v___jp_1285_;
}
else
{
v___y_1286_ = v___y_1297_;
v_fst_1287_ = v___y_1299_;
v_snd_1288_ = v___y_1298_;
goto v___jp_1285_;
}
}
v___jp_1301_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = lean_array_get_size(v_buckets_1303_);
v___x_1308_ = lean_nat_dec_lt(v___x_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v_buckets_1303_);
v___y_1297_ = v___y_1302_;
v___y_1298_ = v___y_1305_;
v___y_1299_ = v___y_1304_;
goto v___jp_1296_;
}
else
{
uint8_t v___x_1309_; 
v___x_1309_ = lean_nat_dec_le(v___x_1307_, v___x_1307_);
if (v___x_1309_ == 0)
{
if (v___x_1308_ == 0)
{
lean_dec_ref(v_buckets_1303_);
v___y_1297_ = v___y_1302_;
v___y_1298_ = v___y_1305_;
v___y_1299_ = v___y_1304_;
goto v___jp_1296_;
}
else
{
size_t v___x_1310_; size_t v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = ((size_t)0ULL);
v___x_1311_ = lean_usize_of_nat(v___x_1307_);
v___x_1312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1303_, v___x_1310_, v___x_1311_, v___y_1304_);
lean_dec_ref(v_buckets_1303_);
v___y_1297_ = v___y_1302_;
v___y_1298_ = v___y_1305_;
v___y_1299_ = v___x_1312_;
goto v___jp_1296_;
}
}
else
{
size_t v___x_1313_; size_t v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = ((size_t)0ULL);
v___x_1314_ = lean_usize_of_nat(v___x_1307_);
v___x_1315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1303_, v___x_1313_, v___x_1314_, v___y_1304_);
lean_dec_ref(v_buckets_1303_);
v___y_1297_ = v___y_1302_;
v___y_1298_ = v___y_1305_;
v___y_1299_ = v___x_1315_;
goto v___jp_1296_;
}
}
}
v___jp_1316_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1322_ = lean_array_get_size(v_buckets_1320_);
v___x_1323_ = lean_nat_dec_lt(v___x_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
v___y_1302_ = v___y_1319_;
v_buckets_1303_ = v_buckets_1320_;
v___y_1304_ = v___y_1318_;
v___y_1305_ = v___y_1317_;
goto v___jp_1301_;
}
else
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_nat_dec_le(v___x_1322_, v___x_1322_);
if (v___x_1324_ == 0)
{
if (v___x_1323_ == 0)
{
v___y_1302_ = v___y_1319_;
v_buckets_1303_ = v_buckets_1320_;
v___y_1304_ = v___y_1318_;
v___y_1305_ = v___y_1317_;
goto v___jp_1301_;
}
else
{
size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = lean_usize_of_nat(v___x_1322_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1320_, v___x_1325_, v___x_1326_, v___y_1317_);
v___y_1302_ = v___y_1319_;
v_buckets_1303_ = v_buckets_1320_;
v___y_1304_ = v___y_1318_;
v___y_1305_ = v___x_1327_;
goto v___jp_1301_;
}
}
else
{
size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = lean_usize_of_nat(v___x_1322_);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1320_, v___x_1328_, v___x_1329_, v___y_1317_);
v___y_1302_ = v___y_1319_;
v_buckets_1303_ = v_buckets_1320_;
v___y_1304_ = v___y_1318_;
v___y_1305_ = v___x_1330_;
goto v___jp_1301_;
}
}
}
v___jp_1331_:
{
lean_object* v_buckets_1335_; 
v_buckets_1335_ = lean_ctor_get(v___y_1334_, 1);
lean_inc_ref(v_buckets_1335_);
v___y_1317_ = v___y_1332_;
v___y_1318_ = v___y_1333_;
v___y_1319_ = v___y_1334_;
v_buckets_1320_ = v_buckets_1335_;
goto v___jp_1316_;
}
v___jp_1336_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v___x_1340_ = lean_unsigned_to_nat(0u);
v___x_1341_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1342_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1343_ = lean_array_get_size(v_buckets_1338_);
v___x_1344_ = lean_nat_dec_lt(v___x_1340_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_dec_ref(v_buckets_1338_);
v___y_1317_ = v_fst_1337_;
v___y_1318_ = v_snd_1339_;
v___y_1319_ = v___x_1342_;
v_buckets_1320_ = v___x_1341_;
goto v___jp_1316_;
}
else
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_nat_dec_le(v___x_1343_, v___x_1343_);
if (v___x_1345_ == 0)
{
if (v___x_1344_ == 0)
{
lean_dec_ref(v_buckets_1338_);
v___y_1317_ = v_fst_1337_;
v___y_1318_ = v_snd_1339_;
v___y_1319_ = v___x_1342_;
v_buckets_1320_ = v___x_1341_;
goto v___jp_1316_;
}
else
{
size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = ((size_t)0ULL);
v___x_1347_ = lean_usize_of_nat(v___x_1343_);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1339_, v_buckets_1338_, v___x_1346_, v___x_1347_, v___x_1342_);
lean_dec_ref(v_buckets_1338_);
v___y_1332_ = v_fst_1337_;
v___y_1333_ = v_snd_1339_;
v___y_1334_ = v___x_1348_;
goto v___jp_1331_;
}
}
else
{
size_t v___x_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = ((size_t)0ULL);
v___x_1350_ = lean_usize_of_nat(v___x_1343_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1339_, v_buckets_1338_, v___x_1349_, v___x_1350_, v___x_1342_);
lean_dec_ref(v_buckets_1338_);
v___y_1332_ = v_fst_1337_;
v___y_1333_ = v_snd_1339_;
v___y_1334_ = v___x_1351_;
goto v___jp_1331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1353_, lean_object* v_y_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1353_, v_y_1354_, v_a_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object* v_x_1358_, lean_object* v_y_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1358_, v_y_1359_, v_a_1360_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1369_, lean_object* v_y_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(v_x_1369_, v_y_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1380_, lean_object* v_m_1381_, lean_object* v_a_1382_, lean_object* v_b_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1381_, v_a_1382_, v_b_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1385_, lean_object* v_m_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1386_, v_a_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1389_, lean_object* v_m_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1389_, v_m_1390_, v_a_1391_);
lean_dec(v_a_1391_);
lean_dec_ref(v_m_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1393_, lean_object* v_a_1394_, lean_object* v_b_1395_, lean_object* v_x_1396_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1394_, v_b_1395_, v_x_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1398_, lean_object* v_a_1399_, lean_object* v_x_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1399_, v_x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1402_, lean_object* v_a_1403_, lean_object* v_x_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1402_, v_a_1403_, v_x_1404_);
lean_dec(v_x_1404_);
lean_dec(v_a_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1406_, lean_object* v_x_1407_){
_start:
{
if (lean_obj_tag(v_x_1407_) == 0)
{
return v_x_1406_;
}
else
{
lean_object* v_key_1408_; lean_object* v_value_1409_; lean_object* v_tail_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v_key_1408_ = lean_ctor_get(v_x_1407_, 0);
v_value_1409_ = lean_ctor_get(v_x_1407_, 1);
v_tail_1410_ = lean_ctor_get(v_x_1407_, 2);
lean_inc(v_value_1409_);
lean_inc(v_key_1408_);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_key_1408_);
lean_ctor_set(v___x_1411_, 1, v_value_1409_);
v___x_1412_ = lean_array_push(v_x_1406_, v___x_1411_);
v_x_1406_ = v___x_1412_;
v_x_1407_ = v_tail_1410_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1414_, lean_object* v_x_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1414_, v_x_1415_);
lean_dec(v_x_1415_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1417_, size_t v_i_1418_, size_t v_stop_1419_, lean_object* v_b_1420_){
_start:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_usize_dec_eq(v_i_1418_, v_stop_1419_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; size_t v___x_1424_; size_t v___x_1425_; 
v___x_1422_ = lean_array_uget_borrowed(v_as_1417_, v_i_1418_);
v___x_1423_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1420_, v___x_1422_);
v___x_1424_ = ((size_t)1ULL);
v___x_1425_ = lean_usize_add(v_i_1418_, v___x_1424_);
v_i_1418_ = v___x_1425_;
v_b_1420_ = v___x_1423_;
goto _start;
}
else
{
return v_b_1420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1427_, lean_object* v_i_1428_, lean_object* v_stop_1429_, lean_object* v_b_1430_){
_start:
{
size_t v_i_boxed_1431_; size_t v_stop_boxed_1432_; lean_object* v_res_1433_; 
v_i_boxed_1431_ = lean_unbox_usize(v_i_1428_);
lean_dec(v_i_1428_);
v_stop_boxed_1432_ = lean_unbox_usize(v_stop_1429_);
lean_dec(v_stop_1429_);
v_res_1433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1427_, v_i_boxed_1431_, v_stop_boxed_1432_, v_b_1430_);
lean_dec_ref(v_as_1427_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1434_, lean_object* v___x_1435_, lean_object* v_op_1436_, lean_object* v_a_1437_, lean_object* v_b_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v___y_1442_; uint8_t v___x_1446_; 
v___x_1446_ = lean_nat_dec_lt(v_a_1437_, v_upperBound_1434_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec(v_a_1437_);
lean_dec_ref(v_op_1436_);
lean_dec_ref(v___x_1435_);
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v_b_1438_);
lean_ctor_set(v___x_1447_, 1, v___y_1439_);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
else
{
if (lean_obj_tag(v_b_1438_) == 0)
{
lean_object* v___x_1449_; 
lean_inc_ref(v___x_1435_);
v___x_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1435_);
v___y_1442_ = v___x_1449_;
goto v___jp_1441_;
}
else
{
lean_object* v_val_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1459_; 
v_val_1450_ = lean_ctor_get(v_b_1438_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_b_1438_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1452_ = v_b_1438_;
v_isShared_1453_ = v_isSharedCheck_1459_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_val_1450_);
lean_dec(v_b_1438_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1459_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
lean_inc_ref(v_op_1436_);
v___x_1454_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_1436_);
lean_inc_ref(v___x_1435_);
v___x_1455_ = l_Lean_mkAppB(v___x_1454_, v_val_1450_, v___x_1435_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1455_);
v___x_1457_ = v___x_1452_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
v___y_1442_ = v___x_1457_;
goto v___jp_1441_;
}
}
}
}
v___jp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_unsigned_to_nat(1u);
v___x_1444_ = lean_nat_add(v_a_1437_, v___x_1443_);
lean_dec(v_a_1437_);
v_a_1437_ = v___x_1444_;
v_b_1438_ = v___y_1442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1460_, lean_object* v___x_1461_, lean_object* v_op_1462_, lean_object* v_a_1463_, lean_object* v_b_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1460_, v___x_1461_, v_op_1462_, v_a_1463_, v_b_1464_, v___y_1465_);
lean_dec(v_upperBound_1460_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1468_, lean_object* v_as_1469_, size_t v_sz_1470_, size_t v_i_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
uint8_t v___x_1481_; 
v___x_1481_ = lean_usize_dec_lt(v_i_1471_, v_sz_1470_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec_ref(v_op_1468_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_b_1472_);
lean_ctor_set(v___x_1482_, 1, v___y_1473_);
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
else
{
lean_object* v_a_1484_; lean_object* v_fst_1485_; lean_object* v_snd_1486_; lean_object* v_varToExpr_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_a_1484_ = lean_array_uget_borrowed(v_as_1469_, v_i_1471_);
v_fst_1485_ = lean_ctor_get(v_a_1484_, 0);
v_snd_1486_ = lean_ctor_get(v_a_1484_, 1);
v_varToExpr_1487_ = lean_ctor_get(v___y_1473_, 2);
v___x_1488_ = l_Lean_instInhabitedExpr;
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = lean_array_get(v___x_1488_, v_varToExpr_1487_, v_fst_1485_);
lean_inc_ref(v_op_1468_);
v___x_1491_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1486_, v___x_1490_, v_op_1468_, v___x_1489_, v_b_1472_, v___y_1473_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v_fst_1493_; lean_object* v_snd_1494_; size_t v___x_1495_; size_t v___x_1496_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v_fst_1493_ = lean_ctor_get(v_a_1492_, 0);
lean_inc(v_fst_1493_);
v_snd_1494_ = lean_ctor_get(v_a_1492_, 1);
lean_inc(v_snd_1494_);
lean_dec(v_a_1492_);
v___x_1495_ = ((size_t)1ULL);
v___x_1496_ = lean_usize_add(v_i_1471_, v___x_1495_);
v_i_1471_ = v___x_1496_;
v_b_1472_ = v_fst_1493_;
v___y_1473_ = v_snd_1494_;
goto _start;
}
else
{
lean_dec_ref(v_op_1468_);
return v___x_1491_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1498_, lean_object* v_as_1499_, lean_object* v_sz_1500_, lean_object* v_i_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
size_t v_sz_boxed_1511_; size_t v_i_boxed_1512_; lean_object* v_res_1513_; 
v_sz_boxed_1511_ = lean_unbox_usize(v_sz_1500_);
lean_dec(v_sz_1500_);
v_i_boxed_1512_ = lean_unbox_usize(v_i_1501_);
lean_dec(v_i_1501_);
v_res_1513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1498_, v_as_1499_, v_sz_boxed_1511_, v_i_boxed_1512_, v_b_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec_ref(v_as_1499_);
return v_res_1513_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1514_, lean_object* v_x2_1515_){
_start:
{
lean_object* v_fst_1516_; lean_object* v_fst_1517_; uint8_t v___x_1518_; 
v_fst_1516_ = lean_ctor_get(v_x1_1514_, 0);
v_fst_1517_ = lean_ctor_get(v_x2_1515_, 0);
v___x_1518_ = lean_nat_dec_lt(v_fst_1516_, v_fst_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1519_, lean_object* v_x2_1520_){
_start:
{
uint8_t v_res_1521_; lean_object* v_r_1522_; 
v_res_1521_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1519_, v_x2_1520_);
lean_dec_ref(v_x2_1520_);
lean_dec_ref(v_x1_1519_);
v_r_1522_ = lean_box(v_res_1521_);
return v_r_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object* v_hi_1523_, lean_object* v_pivot_1524_, lean_object* v_as_1525_, lean_object* v_i_1526_, lean_object* v_k_1527_){
_start:
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_nat_dec_lt(v_k_1527_, v_hi_1523_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_k_1527_);
v___x_1529_ = lean_array_fswap(v_as_1525_, v_i_1526_, v_hi_1523_);
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v_i_1526_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
return v___x_1530_;
}
else
{
lean_object* v___x_1531_; lean_object* v_fst_1532_; lean_object* v_fst_1533_; uint8_t v___x_1534_; 
v___x_1531_ = lean_array_fget_borrowed(v_as_1525_, v_k_1527_);
v_fst_1532_ = lean_ctor_get(v___x_1531_, 0);
v_fst_1533_ = lean_ctor_get(v_pivot_1524_, 0);
v___x_1534_ = lean_nat_dec_lt(v_fst_1532_, v_fst_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_nat_add(v_k_1527_, v___x_1535_);
lean_dec(v_k_1527_);
v_k_1527_ = v___x_1536_;
goto _start;
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1538_ = lean_array_fswap(v_as_1525_, v_i_1526_, v_k_1527_);
v___x_1539_ = lean_unsigned_to_nat(1u);
v___x_1540_ = lean_nat_add(v_i_1526_, v___x_1539_);
lean_dec(v_i_1526_);
v___x_1541_ = lean_nat_add(v_k_1527_, v___x_1539_);
lean_dec(v_k_1527_);
v_as_1525_ = v___x_1538_;
v_i_1526_ = v___x_1540_;
v_k_1527_ = v___x_1541_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object* v_hi_1543_, lean_object* v_pivot_1544_, lean_object* v_as_1545_, lean_object* v_i_1546_, lean_object* v_k_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1543_, v_pivot_1544_, v_as_1545_, v_i_1546_, v_k_1547_);
lean_dec_ref(v_pivot_1544_);
lean_dec(v_hi_1543_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_n_1549_, lean_object* v_as_1550_, lean_object* v_lo_1551_, lean_object* v_hi_1552_){
_start:
{
lean_object* v___y_1554_; uint8_t v___x_1564_; 
v___x_1564_ = lean_nat_dec_lt(v_lo_1551_, v_hi_1552_);
if (v___x_1564_ == 0)
{
lean_dec(v_lo_1551_);
return v_as_1550_;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v_mid_1567_; lean_object* v___y_1569_; lean_object* v___y_1575_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1565_ = lean_nat_add(v_lo_1551_, v_hi_1552_);
v___x_1566_ = lean_unsigned_to_nat(1u);
v_mid_1567_ = lean_nat_shiftr(v___x_1565_, v___x_1566_);
lean_dec(v___x_1565_);
v___x_1580_ = lean_array_fget_borrowed(v_as_1550_, v_mid_1567_);
v___x_1581_ = lean_array_fget_borrowed(v_as_1550_, v_lo_1551_);
v___x_1582_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
v___y_1575_ = v_as_1550_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_array_fswap(v_as_1550_, v_lo_1551_, v_mid_1567_);
v___y_1575_ = v___x_1583_;
goto v___jp_1574_;
}
v___jp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1570_ = lean_array_fget_borrowed(v___y_1569_, v_mid_1567_);
v___x_1571_ = lean_array_fget_borrowed(v___y_1569_, v_hi_1552_);
v___x_1572_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1570_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_dec(v_mid_1567_);
v___y_1554_ = v___y_1569_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_array_fswap(v___y_1569_, v_mid_1567_, v_hi_1552_);
lean_dec(v_mid_1567_);
v___y_1554_ = v___x_1573_;
goto v___jp_1553_;
}
}
v___jp_1574_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1576_ = lean_array_fget_borrowed(v___y_1575_, v_hi_1552_);
v___x_1577_ = lean_array_fget_borrowed(v___y_1575_, v_lo_1551_);
v___x_1578_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1576_, v___x_1577_);
if (v___x_1578_ == 0)
{
v___y_1569_ = v___y_1575_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_array_fswap(v___y_1575_, v_lo_1551_, v_hi_1552_);
v___y_1569_ = v___x_1579_;
goto v___jp_1568_;
}
}
}
v___jp_1553_:
{
lean_object* v_pivot_1555_; lean_object* v___x_1556_; lean_object* v_fst_1557_; lean_object* v_snd_1558_; uint8_t v___x_1559_; 
v_pivot_1555_ = lean_array_fget(v___y_1554_, v_hi_1552_);
lean_inc_n(v_lo_1551_, 2);
v___x_1556_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1552_, v_pivot_1555_, v___y_1554_, v_lo_1551_, v_lo_1551_);
lean_dec(v_pivot_1555_);
v_fst_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_fst_1557_);
v_snd_1558_ = lean_ctor_get(v___x_1556_, 1);
lean_inc(v_snd_1558_);
lean_dec_ref(v___x_1556_);
v___x_1559_ = lean_nat_dec_le(v_hi_1552_, v_fst_1557_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1549_, v_snd_1558_, v_lo_1551_, v_fst_1557_);
v___x_1561_ = lean_unsigned_to_nat(1u);
v___x_1562_ = lean_nat_add(v_fst_1557_, v___x_1561_);
lean_dec(v_fst_1557_);
v_as_1550_ = v___x_1560_;
v_lo_1551_ = v___x_1562_;
goto _start;
}
else
{
lean_dec(v_fst_1557_);
lean_dec(v_lo_1551_);
return v_snd_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_n_1584_, lean_object* v_as_1585_, lean_object* v_lo_1586_, lean_object* v_hi_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1584_, v_as_1585_, v_lo_1586_, v_hi_1587_);
lean_dec(v_hi_1587_);
lean_dec(v_n_1584_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1589_, lean_object* v_op_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___y_1600_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1618_; lean_object* v_size_1625_; lean_object* v_buckets_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v_size_1625_ = lean_ctor_get(v_coeff_1589_, 0);
v_buckets_1626_ = lean_ctor_get(v_coeff_1589_, 1);
v___x_1627_ = lean_mk_empty_array_with_capacity(v_size_1625_);
v___x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = lean_array_get_size(v_buckets_1626_);
v___x_1630_ = lean_nat_dec_lt(v___x_1628_, v___x_1629_);
if (v___x_1630_ == 0)
{
v___y_1618_ = v___x_1627_;
goto v___jp_1617_;
}
else
{
uint8_t v___x_1631_; 
v___x_1631_ = lean_nat_dec_le(v___x_1629_, v___x_1629_);
if (v___x_1631_ == 0)
{
if (v___x_1630_ == 0)
{
v___y_1618_ = v___x_1627_;
goto v___jp_1617_;
}
else
{
size_t v___x_1632_; size_t v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = ((size_t)0ULL);
v___x_1633_ = lean_usize_of_nat(v___x_1629_);
v___x_1634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1626_, v___x_1632_, v___x_1633_, v___x_1627_);
v___y_1618_ = v___x_1634_;
goto v___jp_1617_;
}
}
else
{
size_t v___x_1635_; size_t v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = ((size_t)0ULL);
v___x_1636_ = lean_usize_of_nat(v___x_1629_);
v___x_1637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1626_, v___x_1635_, v___x_1636_, v___x_1627_);
v___y_1618_ = v___x_1637_;
goto v___jp_1617_;
}
}
v___jp_1599_:
{
lean_object* v_acc_1601_; size_t v_sz_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
v_acc_1601_ = lean_box(0);
v_sz_1602_ = lean_array_size(v___y_1600_);
v___x_1603_ = ((size_t)0ULL);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1590_, v___y_1600_, v_sz_1602_, v___x_1603_, v_acc_1601_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
lean_dec_ref(v___y_1600_);
return v___x_1604_;
}
v___jp_1605_:
{
lean_object* v___x_1610_; 
v___x_1610_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec(v___y_1606_);
v___y_1600_ = v___x_1610_;
goto v___jp_1599_;
}
v___jp_1611_:
{
uint8_t v___x_1616_; 
v___x_1616_ = lean_nat_dec_le(v___y_1615_, v___y_1612_);
if (v___x_1616_ == 0)
{
lean_dec(v___y_1612_);
lean_inc(v___y_1615_);
v___y_1606_ = v___y_1613_;
v___y_1607_ = v___y_1614_;
v___y_1608_ = v___y_1615_;
v___y_1609_ = v___y_1615_;
goto v___jp_1605_;
}
else
{
v___y_1606_ = v___y_1613_;
v___y_1607_ = v___y_1614_;
v___y_1608_ = v___y_1615_;
v___y_1609_ = v___y_1612_;
goto v___jp_1605_;
}
}
v___jp_1617_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1619_ = lean_array_get_size(v___y_1618_);
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = lean_nat_dec_eq(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1622_ = lean_unsigned_to_nat(1u);
v___x_1623_ = lean_nat_sub(v___x_1619_, v___x_1622_);
v___x_1624_ = lean_nat_dec_le(v___x_1620_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_inc(v___x_1623_);
v___y_1612_ = v___x_1623_;
v___y_1613_ = v___x_1619_;
v___y_1614_ = v___y_1618_;
v___y_1615_ = v___x_1623_;
goto v___jp_1611_;
}
else
{
v___y_1612_ = v___x_1623_;
v___y_1613_ = v___x_1619_;
v___y_1614_ = v___y_1618_;
v___y_1615_ = v___x_1620_;
goto v___jp_1611_;
}
}
else
{
v___y_1600_ = v___y_1618_;
goto v___jp_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1638_, lean_object* v_op_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_coeff_1638_, v_op_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec_ref(v_coeff_1638_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1649_, lean_object* v___x_1650_, lean_object* v_op_1651_, lean_object* v_inst_1652_, lean_object* v_R_1653_, lean_object* v_a_1654_, lean_object* v_b_1655_, lean_object* v_c_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1649_, v___x_1650_, v_op_1651_, v_a_1654_, v_b_1655_, v___y_1657_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1666_, lean_object* v___x_1667_, lean_object* v_op_1668_, lean_object* v_inst_1669_, lean_object* v_R_1670_, lean_object* v_a_1671_, lean_object* v_b_1672_, lean_object* v_c_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1666_, v___x_1667_, v_op_1668_, v_inst_1669_, v_R_1670_, v_a_1671_, v_b_1672_, v_c_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v_upperBound_1666_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1683_, lean_object* v_as_1684_, lean_object* v_lo_1685_, lean_object* v_hi_1686_, lean_object* v_w_1687_, lean_object* v_hlo_1688_, lean_object* v_hhi_1689_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1683_, v_as_1684_, v_lo_1685_, v_hi_1686_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1691_, lean_object* v_as_1692_, lean_object* v_lo_1693_, lean_object* v_hi_1694_, lean_object* v_w_1695_, lean_object* v_hlo_1696_, lean_object* v_hhi_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1691_, v_as_1692_, v_lo_1693_, v_hi_1694_, v_w_1695_, v_hlo_1696_, v_hhi_1697_);
lean_dec(v_hi_1694_);
lean_dec(v_n_1691_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object* v_n_1699_, lean_object* v_lo_1700_, lean_object* v_hi_1701_, lean_object* v_hhi_1702_, lean_object* v_pivot_1703_, lean_object* v_as_1704_, lean_object* v_i_1705_, lean_object* v_k_1706_, lean_object* v_ilo_1707_, lean_object* v_ik_1708_, lean_object* v_w_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1701_, v_pivot_1703_, v_as_1704_, v_i_1705_, v_k_1706_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object* v_n_1711_, lean_object* v_lo_1712_, lean_object* v_hi_1713_, lean_object* v_hhi_1714_, lean_object* v_pivot_1715_, lean_object* v_as_1716_, lean_object* v_i_1717_, lean_object* v_k_1718_, lean_object* v_ilo_1719_, lean_object* v_ik_1720_, lean_object* v_w_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_n_1711_, v_lo_1712_, v_hi_1713_, v_hhi_1714_, v_pivot_1715_, v_as_1716_, v_i_1717_, v_k_1718_, v_ilo_1719_, v_ik_1720_, v_w_1721_);
lean_dec_ref(v_pivot_1715_);
lean_dec(v_hi_1713_);
lean_dec(v_lo_1712_);
lean_dec(v_n_1711_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1723_, lean_object* v___y_1724_){
_start:
{
uint8_t v___x_1726_; 
v___x_1726_ = l_Lean_Expr_hasMVar(v_e_1723_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v_e_1723_);
return v___x_1727_;
}
else
{
lean_object* v___x_1728_; lean_object* v_mctx_1729_; lean_object* v___x_1730_; lean_object* v_fst_1731_; lean_object* v_snd_1732_; lean_object* v___x_1733_; lean_object* v_cache_1734_; lean_object* v_zetaDeltaFVarIds_1735_; lean_object* v_postponed_1736_; lean_object* v_diag_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1746_; 
v___x_1728_ = lean_st_ref_get(v___y_1724_);
v_mctx_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc_ref(v_mctx_1729_);
lean_dec(v___x_1728_);
v___x_1730_ = l_Lean_instantiateMVarsCore(v_mctx_1729_, v_e_1723_);
v_fst_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_fst_1731_);
v_snd_1732_ = lean_ctor_get(v___x_1730_, 1);
lean_inc(v_snd_1732_);
lean_dec_ref(v___x_1730_);
v___x_1733_ = lean_st_ref_take(v___y_1724_);
v_cache_1734_ = lean_ctor_get(v___x_1733_, 1);
v_zetaDeltaFVarIds_1735_ = lean_ctor_get(v___x_1733_, 2);
v_postponed_1736_ = lean_ctor_get(v___x_1733_, 3);
v_diag_1737_ = lean_ctor_get(v___x_1733_, 4);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; 
v_unused_1747_ = lean_ctor_get(v___x_1733_, 0);
lean_dec(v_unused_1747_);
v___x_1739_ = v___x_1733_;
v_isShared_1740_ = v_isSharedCheck_1746_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_diag_1737_);
lean_inc(v_postponed_1736_);
lean_inc(v_zetaDeltaFVarIds_1735_);
lean_inc(v_cache_1734_);
lean_dec(v___x_1733_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1746_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v_snd_1732_);
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_snd_1732_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_cache_1734_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_zetaDeltaFVarIds_1735_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_postponed_1736_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v_diag_1737_);
v___x_1742_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_st_ref_set(v___y_1724_, v___x_1742_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_fst_1731_);
return v___x_1744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1748_, v___y_1749_);
lean_dec(v___y_1749_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1752_, v___y_1754_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(v_e_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object* v_x_1766_, lean_object* v_y_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_Meta_mkEq(v_x_1766_, v_y_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1796_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1796_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1796_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set_tag(v___x_1776_, 1);
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = 0;
v___x_1781_ = lean_box(0);
v___x_1782_ = l_Lean_Meta_mkFreshExprMVar(v___x_1779_, v___x_1780_, v___x_1781_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v___x_1784_ = l_Lean_Expr_mvarId_x21(v_a_1783_);
v___x_1785_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1784_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v___x_1786_; 
lean_dec_ref_known(v___x_1785_, 1);
v___x_1786_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1783_, v_a_1769_);
return v___x_1786_;
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_a_1783_);
v_a_1787_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1785_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1785_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
return v___x_1782_;
}
}
}
}
else
{
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1797_, lean_object* v_y_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v_x_1797_, v_y_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
return v_res_1804_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = lean_unsigned_to_nat(32u);
v___x_1806_ = lean_mk_empty_array_with_capacity(v___x_1805_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1808_ = ((size_t)5ULL);
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = lean_unsigned_to_nat(32u);
v___x_1811_ = lean_mk_empty_array_with_capacity(v___x_1810_);
v___x_1812_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1813_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___x_1811_);
lean_ctor_set(v___x_1813_, 2, v___x_1809_);
lean_ctor_set(v___x_1813_, 3, v___x_1809_);
lean_ctor_set_usize(v___x_1813_, 4, v___x_1808_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; lean_object* v_traceState_1817_; lean_object* v_traces_1818_; lean_object* v___x_1819_; lean_object* v_traceState_1820_; lean_object* v_env_1821_; lean_object* v_nextMacroScope_1822_; lean_object* v_ngen_1823_; lean_object* v_auxDeclNGen_1824_; lean_object* v_cache_1825_; lean_object* v_messages_1826_; lean_object* v_infoState_1827_; lean_object* v_snapshotTasks_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1847_; 
v___x_1816_ = lean_st_ref_get(v___y_1814_);
v_traceState_1817_ = lean_ctor_get(v___x_1816_, 4);
lean_inc_ref(v_traceState_1817_);
lean_dec(v___x_1816_);
v_traces_1818_ = lean_ctor_get(v_traceState_1817_, 0);
lean_inc_ref(v_traces_1818_);
lean_dec_ref(v_traceState_1817_);
v___x_1819_ = lean_st_ref_take(v___y_1814_);
v_traceState_1820_ = lean_ctor_get(v___x_1819_, 4);
v_env_1821_ = lean_ctor_get(v___x_1819_, 0);
v_nextMacroScope_1822_ = lean_ctor_get(v___x_1819_, 1);
v_ngen_1823_ = lean_ctor_get(v___x_1819_, 2);
v_auxDeclNGen_1824_ = lean_ctor_get(v___x_1819_, 3);
v_cache_1825_ = lean_ctor_get(v___x_1819_, 5);
v_messages_1826_ = lean_ctor_get(v___x_1819_, 6);
v_infoState_1827_ = lean_ctor_get(v___x_1819_, 7);
v_snapshotTasks_1828_ = lean_ctor_get(v___x_1819_, 8);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1830_ = v___x_1819_;
v_isShared_1831_ = v_isSharedCheck_1847_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_snapshotTasks_1828_);
lean_inc(v_infoState_1827_);
lean_inc(v_messages_1826_);
lean_inc(v_cache_1825_);
lean_inc(v_traceState_1820_);
lean_inc(v_auxDeclNGen_1824_);
lean_inc(v_ngen_1823_);
lean_inc(v_nextMacroScope_1822_);
lean_inc(v_env_1821_);
lean_dec(v___x_1819_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1847_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
uint64_t v_tid_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1845_; 
v_tid_1832_ = lean_ctor_get_uint64(v_traceState_1820_, sizeof(void*)*1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_traceState_1820_);
if (v_isSharedCheck_1845_ == 0)
{
lean_object* v_unused_1846_; 
v_unused_1846_ = lean_ctor_get(v_traceState_1820_, 0);
lean_dec(v_unused_1846_);
v___x_1834_ = v_traceState_1820_;
v_isShared_1835_ = v_isSharedCheck_1845_;
goto v_resetjp_1833_;
}
else
{
lean_dec(v_traceState_1820_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1845_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1836_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1836_);
v___x_1838_ = v___x_1834_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1836_);
lean_ctor_set_uint64(v_reuseFailAlloc_1844_, sizeof(void*)*1, v_tid_1832_);
v___x_1838_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1840_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 4, v___x_1838_);
v___x_1840_ = v___x_1830_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_env_1821_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_nextMacroScope_1822_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_ngen_1823_);
lean_ctor_set(v_reuseFailAlloc_1843_, 3, v_auxDeclNGen_1824_);
lean_ctor_set(v_reuseFailAlloc_1843_, 4, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1843_, 5, v_cache_1825_);
lean_ctor_set(v_reuseFailAlloc_1843_, 6, v_messages_1826_);
lean_ctor_set(v_reuseFailAlloc_1843_, 7, v_infoState_1827_);
lean_ctor_set(v_reuseFailAlloc_1843_, 8, v_snapshotTasks_1828_);
v___x_1840_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_st_ref_set(v___y_1814_, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_traces_1818_);
return v___x_1842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1848_);
lean_dec(v___y_1848_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1859_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
return v_res_1872_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1873_, lean_object* v_opt_1874_){
_start:
{
lean_object* v_name_1875_; lean_object* v_defValue_1876_; lean_object* v_map_1877_; lean_object* v___x_1878_; 
v_name_1875_ = lean_ctor_get(v_opt_1874_, 0);
v_defValue_1876_ = lean_ctor_get(v_opt_1874_, 1);
v_map_1877_ = lean_ctor_get(v_opts_1873_, 0);
v___x_1878_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1877_, v_name_1875_);
if (lean_obj_tag(v___x_1878_) == 0)
{
uint8_t v___x_1879_; 
v___x_1879_ = lean_unbox(v_defValue_1876_);
return v___x_1879_;
}
else
{
lean_object* v_val_1880_; 
v_val_1880_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_val_1880_);
lean_dec_ref_known(v___x_1878_, 1);
if (lean_obj_tag(v_val_1880_) == 1)
{
uint8_t v_v_1881_; 
v_v_1881_ = lean_ctor_get_uint8(v_val_1880_, 0);
lean_dec_ref_known(v_val_1880_, 0);
return v_v_1881_;
}
else
{
uint8_t v___x_1882_; 
lean_dec(v_val_1880_);
v___x_1882_ = lean_unbox(v_defValue_1876_);
return v___x_1882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1883_, lean_object* v_opt_1884_){
_start:
{
uint8_t v_res_1885_; lean_object* v_r_1886_; 
v_res_1885_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_1883_, v_opt_1884_);
lean_dec_ref(v_opt_1884_);
lean_dec_ref(v_opts_1883_);
v_r_1886_ = lean_box(v_res_1885_);
return v_r_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1887_, lean_object* v_____do__lift_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_options_1899_; uint8_t v_hasTrace_1900_; 
v_options_1899_ = lean_ctor_get(v___y_1896_, 2);
v_hasTrace_1900_ = lean_ctor_get_uint8(v_options_1899_, sizeof(void*)*1);
if (v_hasTrace_1900_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec(v_cls_1887_);
v___x_1901_ = lean_box(v_hasTrace_1900_);
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1904_ = l_Lean_Name_append(v___x_1903_, v_cls_1887_);
v___x_1905_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1888_, v_options_1899_, v___x_1904_);
lean_dec(v___x_1904_);
v___x_1906_ = lean_box(v___x_1905_);
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
return v___x_1907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1908_, lean_object* v_____do__lift_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_1908_, v_____do__lift_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v_____do__lift_1909_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_mkAppB(v___x_1921_, v___y_1922_, v___y_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1925_, lean_object* v_lhs_1926_, lean_object* v_rhs_1927_, lean_object* v_P_1928_, uint8_t v___x_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; 
lean_inc_ref(v_lhs_1926_);
lean_inc_ref(v_val_1925_);
v___x_1938_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1925_, v_lhs_1926_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v_fst_1940_; lean_object* v_snd_1941_; lean_object* v___x_1942_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v_fst_1940_ = lean_ctor_get(v_a_1939_, 0);
lean_inc(v_fst_1940_);
v_snd_1941_ = lean_ctor_get(v_a_1939_, 1);
lean_inc(v_snd_1941_);
lean_dec(v_a_1939_);
lean_inc_ref(v_rhs_1927_);
lean_inc_ref(v_val_1925_);
v___x_1942_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1925_, v_rhs_1927_, v_snd_1941_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v_fst_1944_; lean_object* v_snd_1945_; lean_object* v___x_1946_; lean_object* v_a_1947_; lean_object* v_fst_1948_; lean_object* v_snd_1949_; lean_object* v_common_1950_; lean_object* v_x_1951_; lean_object* v_y_1952_; lean_object* v___x_1953_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v_fst_1944_ = lean_ctor_get(v_a_1943_, 0);
lean_inc(v_fst_1944_);
v_snd_1945_ = lean_ctor_get(v_a_1943_, 1);
lean_inc(v_snd_1945_);
lean_dec(v_a_1943_);
v___x_1946_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_1940_, v_fst_1944_, v_snd_1945_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref(v___x_1946_);
v_fst_1948_ = lean_ctor_get(v_a_1947_, 0);
lean_inc(v_fst_1948_);
v_snd_1949_ = lean_ctor_get(v_a_1947_, 1);
lean_inc(v_snd_1949_);
lean_dec(v_a_1947_);
v_common_1950_ = lean_ctor_get(v_fst_1948_, 0);
lean_inc_ref(v_common_1950_);
v_x_1951_ = lean_ctor_get(v_fst_1948_, 1);
lean_inc_ref(v_x_1951_);
v_y_1952_ = lean_ctor_get(v_fst_1948_, 2);
lean_inc_ref(v_y_1952_);
lean_dec(v_fst_1948_);
lean_inc_ref(v_val_1925_);
v___x_1953_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_1950_, v_val_1925_, v_snd_1949_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec_ref(v_common_1950_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v_fst_1955_; lean_object* v_snd_1956_; lean_object* v___x_1957_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v_fst_1955_ = lean_ctor_get(v_a_1954_, 0);
lean_inc(v_fst_1955_);
v_snd_1956_ = lean_ctor_get(v_a_1954_, 1);
lean_inc(v_snd_1956_);
lean_dec(v_a_1954_);
lean_inc_ref(v_val_1925_);
v___x_1957_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_1951_, v_val_1925_, v_snd_1956_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec_ref(v_x_1951_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v_fst_1959_; lean_object* v_snd_1960_; lean_object* v___x_1961_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v_fst_1959_ = lean_ctor_get(v_a_1958_, 0);
lean_inc(v_fst_1959_);
v_snd_1960_ = lean_ctor_get(v_a_1958_, 1);
lean_inc(v_snd_1960_);
lean_dec(v_a_1958_);
lean_inc_ref(v_val_1925_);
v___x_1961_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_1952_, v_val_1925_, v_snd_1960_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec_ref(v_y_1952_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_2026_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_2026_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_2026_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v_fst_1966_; lean_object* v_snd_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2025_; 
v_fst_1966_ = lean_ctor_get(v_a_1962_, 0);
v_snd_1967_ = lean_ctor_get(v_a_1962_, 1);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_a_1962_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_1969_ = v_a_1962_;
v_isShared_1970_ = v_isSharedCheck_2025_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_snd_1967_);
lean_inc(v_fst_1966_);
lean_dec(v_a_1962_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2025_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___y_2018_; lean_object* v___x_2022_; 
lean_inc_ref(v_val_1925_);
v___x_2015_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_1925_);
v___f_2016_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2016_, 0, v___x_2015_);
lean_inc(v_fst_1955_);
lean_inc_ref(v___f_2016_);
v___x_2022_ = l_Option_merge___redArg(v___f_2016_, v_fst_1955_, v_fst_1959_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v___x_2023_; 
lean_inc_ref(v_val_1925_);
v___x_2023_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1925_);
v___y_2018_ = v___x_2023_;
goto v___jp_2017_;
}
else
{
lean_object* v_val_2024_; 
v_val_2024_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_val_2024_);
lean_dec_ref_known(v___x_2022_, 1);
v___y_2018_ = v_val_2024_;
goto v___jp_2017_;
}
v___jp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
lean_inc_ref(v_P_1928_);
v___x_1974_ = l_Lean_mkAppB(v_P_1928_, v_lhs_1926_, v_rhs_1927_);
v___x_1975_ = l_Lean_mkAppB(v_P_1928_, v___y_1972_, v___y_1973_);
v___x_1976_ = lean_expr_eqv(v___x_1974_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_del_object(v___x_1964_);
lean_inc_ref(v___x_1975_);
v___x_1977_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_1974_, v___x_1975_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1979_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1975_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1991_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1991_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1991_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1984_, 0, v_a_1980_);
lean_ctor_set(v___x_1984_, 1, v_a_1978_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*2, v___x_1976_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*2 + 1, v___x_1976_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1984_);
v___x_1986_ = v___x_1969_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_snd_1967_);
v___x_1986_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1988_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1986_);
v___x_1988_ = v___x_1982_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_a_1978_);
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
v_a_1992_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1979_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1979_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec_ref(v___x_1975_);
lean_del_object(v___x_1969_);
lean_dec(v_snd_1967_);
v_a_2000_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1977_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1977_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
lean_dec_ref(v___x_1975_);
lean_dec_ref(v___x_1974_);
v___x_2008_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2008_, 0, v___x_1929_);
lean_ctor_set_uint8(v___x_2008_, 1, v___x_1929_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_2008_);
v___x_2010_ = v___x_1969_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_snd_1967_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_2010_);
v___x_2012_ = v___x_1964_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
v___jp_2017_:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Option_merge___redArg(v___f_2016_, v_fst_1955_, v_fst_1966_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1925_);
v___y_1972_ = v___y_2018_;
v___y_1973_ = v___x_2020_;
goto v___jp_1971_;
}
else
{
lean_object* v_val_2021_; 
lean_dec_ref(v_val_1925_);
v_val_2021_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_val_2021_);
lean_dec_ref_known(v___x_2019_, 1);
v___y_1972_ = v___y_2018_;
v___y_1973_ = v_val_2021_;
goto v___jp_1971_;
}
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v_fst_1959_);
lean_dec(v_fst_1955_);
lean_dec_ref(v_P_1928_);
lean_dec_ref(v_rhs_1927_);
lean_dec_ref(v_lhs_1926_);
lean_dec_ref(v_val_1925_);
v_a_2027_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_1961_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_1961_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec(v_fst_1955_);
lean_dec_ref(v_y_1952_);
lean_dec_ref(v_P_1928_);
lean_dec_ref(v_rhs_1927_);
lean_dec_ref(v_lhs_1926_);
lean_dec_ref(v_val_1925_);
v_a_2035_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_1957_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_1957_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v_y_1952_);
lean_dec_ref(v_x_1951_);
lean_dec_ref(v_P_1928_);
lean_dec_ref(v_rhs_1927_);
lean_dec_ref(v_lhs_1926_);
lean_dec_ref(v_val_1925_);
v_a_2043_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_1953_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_1953_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_fst_1940_);
lean_dec_ref(v_P_1928_);
lean_dec_ref(v_rhs_1927_);
lean_dec_ref(v_lhs_1926_);
lean_dec_ref(v_val_1925_);
v_a_2051_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_1942_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_1942_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_P_1928_);
lean_dec_ref(v_rhs_1927_);
lean_dec_ref(v_lhs_1926_);
lean_dec_ref(v_val_1925_);
v_a_2059_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_1938_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_1938_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_2067_, lean_object* v_lhs_2068_, lean_object* v_rhs_2069_, lean_object* v_P_2070_, lean_object* v___x_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
uint8_t v___x_209857__boxed_2080_; lean_object* v_res_2081_; 
v___x_209857__boxed_2080_ = lean_unbox(v___x_2071_);
v_res_2081_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(v_val_2067_, v_lhs_2068_, v_rhs_2069_, v_P_2070_, v___x_209857__boxed_2080_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
return v_res_2081_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2084_ = l_Lean_stringToMessageData(v___x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(v_x_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v_x_2098_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object* v_val_2110_, lean_object* v_lhs_2111_, lean_object* v_rhs_2112_, lean_object* v_P_2113_, uint8_t v___x_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; 
lean_inc_ref(v_lhs_2111_);
lean_inc_ref(v_val_2110_);
v___x_2123_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2110_, v_lhs_2111_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v_fst_2125_; lean_object* v_snd_2126_; lean_object* v___x_2127_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v_fst_2125_ = lean_ctor_get(v_a_2124_, 0);
lean_inc(v_fst_2125_);
v_snd_2126_ = lean_ctor_get(v_a_2124_, 1);
lean_inc(v_snd_2126_);
lean_dec(v_a_2124_);
lean_inc_ref(v_rhs_2112_);
lean_inc_ref(v_val_2110_);
v___x_2127_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2110_, v_rhs_2112_, v_snd_2126_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v_fst_2129_; lean_object* v_snd_2130_; lean_object* v___x_2131_; lean_object* v_a_2132_; lean_object* v_fst_2133_; lean_object* v_snd_2134_; lean_object* v_common_2135_; lean_object* v_x_2136_; lean_object* v_y_2137_; lean_object* v___x_2138_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v_fst_2129_ = lean_ctor_get(v_a_2128_, 0);
lean_inc(v_fst_2129_);
v_snd_2130_ = lean_ctor_get(v_a_2128_, 1);
lean_inc(v_snd_2130_);
lean_dec(v_a_2128_);
v___x_2131_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_2125_, v_fst_2129_, v_snd_2130_);
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref(v___x_2131_);
v_fst_2133_ = lean_ctor_get(v_a_2132_, 0);
lean_inc(v_fst_2133_);
v_snd_2134_ = lean_ctor_get(v_a_2132_, 1);
lean_inc(v_snd_2134_);
lean_dec(v_a_2132_);
v_common_2135_ = lean_ctor_get(v_fst_2133_, 0);
lean_inc_ref(v_common_2135_);
v_x_2136_ = lean_ctor_get(v_fst_2133_, 1);
lean_inc_ref(v_x_2136_);
v_y_2137_ = lean_ctor_get(v_fst_2133_, 2);
lean_inc_ref(v_y_2137_);
lean_dec(v_fst_2133_);
lean_inc_ref(v_val_2110_);
v___x_2138_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_2135_, v_val_2110_, v_snd_2134_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec_ref(v_common_2135_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v_fst_2140_; lean_object* v_snd_2141_; lean_object* v___x_2142_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v_fst_2140_ = lean_ctor_get(v_a_2139_, 0);
lean_inc(v_fst_2140_);
v_snd_2141_ = lean_ctor_get(v_a_2139_, 1);
lean_inc(v_snd_2141_);
lean_dec(v_a_2139_);
lean_inc_ref(v_val_2110_);
v___x_2142_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_2136_, v_val_2110_, v_snd_2141_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec_ref(v_x_2136_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v_fst_2144_; lean_object* v_snd_2145_; lean_object* v___x_2146_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v_fst_2144_ = lean_ctor_get(v_a_2143_, 0);
lean_inc(v_fst_2144_);
v_snd_2145_ = lean_ctor_get(v_a_2143_, 1);
lean_inc(v_snd_2145_);
lean_dec(v_a_2143_);
lean_inc_ref(v_val_2110_);
v___x_2146_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_2137_, v_val_2110_, v_snd_2145_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec_ref(v_y_2137_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2211_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2149_ = v___x_2146_;
v_isShared_2150_ = v_isSharedCheck_2211_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2146_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2211_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v_fst_2151_; lean_object* v_snd_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2210_; 
v_fst_2151_ = lean_ctor_get(v_a_2147_, 0);
v_snd_2152_ = lean_ctor_get(v_a_2147_, 1);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_a_2147_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2154_ = v_a_2147_;
v_isShared_2155_ = v_isSharedCheck_2210_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_snd_2152_);
lean_inc(v_fst_2151_);
lean_dec(v_a_2147_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2210_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___x_2200_; lean_object* v___f_2201_; lean_object* v___y_2203_; lean_object* v___x_2207_; 
lean_inc_ref(v_val_2110_);
v___x_2200_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2110_);
v___f_2201_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2201_, 0, v___x_2200_);
lean_inc(v_fst_2140_);
lean_inc_ref(v___f_2201_);
v___x_2207_ = l_Option_merge___redArg(v___f_2201_, v_fst_2140_, v_fst_2144_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v___x_2208_; 
lean_inc_ref(v_val_2110_);
v___x_2208_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2110_);
v___y_2203_ = v___x_2208_;
goto v___jp_2202_;
}
else
{
lean_object* v_val_2209_; 
v_val_2209_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_val_2209_);
lean_dec_ref_known(v___x_2207_, 1);
v___y_2203_ = v_val_2209_;
goto v___jp_2202_;
}
v___jp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
lean_inc_ref(v_P_2113_);
v___x_2159_ = l_Lean_mkAppB(v_P_2113_, v_lhs_2111_, v_rhs_2112_);
v___x_2160_ = l_Lean_mkAppB(v_P_2113_, v___y_2157_, v___y_2158_);
v___x_2161_ = lean_expr_eqv(v___x_2159_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; 
lean_del_object(v___x_2149_);
lean_inc_ref(v___x_2160_);
v___x_2162_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_2159_, v___x_2160_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2164_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2164_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2160_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2176_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2176_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2176_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2169_, 0, v_a_2165_);
lean_ctor_set(v___x_2169_, 1, v_a_2163_);
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*2, v___x_2114_);
lean_ctor_set_uint8(v___x_2169_, sizeof(void*)*2 + 1, v___x_2114_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2169_);
v___x_2171_ = v___x_2154_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_snd_2152_);
v___x_2171_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2173_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2171_);
v___x_2173_ = v___x_2167_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_a_2163_);
lean_del_object(v___x_2154_);
lean_dec(v_snd_2152_);
v_a_2177_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2164_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2164_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref(v___x_2160_);
lean_del_object(v___x_2154_);
lean_dec(v_snd_2152_);
v_a_2185_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2162_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2162_);
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
else
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
lean_dec_ref(v___x_2160_);
lean_dec_ref(v___x_2159_);
v___x_2193_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2193_, 0, v___x_2114_);
lean_ctor_set_uint8(v___x_2193_, 1, v___x_2114_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2193_);
v___x_2195_ = v___x_2154_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_snd_2152_);
v___x_2195_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2197_; 
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2195_);
v___x_2197_ = v___x_2149_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
v___jp_2202_:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Option_merge___redArg(v___f_2201_, v_fst_2140_, v_fst_2151_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2110_);
v___y_2157_ = v___y_2203_;
v___y_2158_ = v___x_2205_;
goto v___jp_2156_;
}
else
{
lean_object* v_val_2206_; 
lean_dec_ref(v_val_2110_);
v_val_2206_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_val_2206_);
lean_dec_ref_known(v___x_2204_, 1);
v___y_2157_ = v___y_2203_;
v___y_2158_ = v_val_2206_;
goto v___jp_2156_;
}
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_fst_2144_);
lean_dec(v_fst_2140_);
lean_dec_ref(v_P_2113_);
lean_dec_ref(v_rhs_2112_);
lean_dec_ref(v_lhs_2111_);
lean_dec_ref(v_val_2110_);
v_a_2212_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2146_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2146_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_fst_2140_);
lean_dec_ref(v_y_2137_);
lean_dec_ref(v_P_2113_);
lean_dec_ref(v_rhs_2112_);
lean_dec_ref(v_lhs_2111_);
lean_dec_ref(v_val_2110_);
v_a_2220_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2142_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2142_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec_ref(v_y_2137_);
lean_dec_ref(v_x_2136_);
lean_dec_ref(v_P_2113_);
lean_dec_ref(v_rhs_2112_);
lean_dec_ref(v_lhs_2111_);
lean_dec_ref(v_val_2110_);
v_a_2228_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2138_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2138_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v_fst_2125_);
lean_dec_ref(v_P_2113_);
lean_dec_ref(v_rhs_2112_);
lean_dec_ref(v_lhs_2111_);
lean_dec_ref(v_val_2110_);
v_a_2236_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2127_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2127_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec_ref(v_P_2113_);
lean_dec_ref(v_rhs_2112_);
lean_dec_ref(v_lhs_2111_);
lean_dec_ref(v_val_2110_);
v_a_2244_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2123_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2123_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object* v_val_2252_, lean_object* v_lhs_2253_, lean_object* v_rhs_2254_, lean_object* v_P_2255_, lean_object* v___x_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
uint8_t v___x_210192__boxed_2265_; lean_object* v_res_2266_; 
v___x_210192__boxed_2265_ = lean_unbox(v___x_2256_);
v_res_2266_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(v_val_2252_, v_lhs_2253_, v_rhs_2254_, v_P_2255_, v___x_210192__boxed_2265_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2267_, lean_object* v_msg_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_ref_2274_; lean_object* v___x_2275_; lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2320_; 
v_ref_2274_ = lean_ctor_get(v___y_2271_, 5);
v___x_2275_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2278_ = v___x_2275_;
v_isShared_2279_ = v_isSharedCheck_2320_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2320_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v_traceState_2281_; lean_object* v_env_2282_; lean_object* v_nextMacroScope_2283_; lean_object* v_ngen_2284_; lean_object* v_auxDeclNGen_2285_; lean_object* v_cache_2286_; lean_object* v_messages_2287_; lean_object* v_infoState_2288_; lean_object* v_snapshotTasks_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2319_; 
v___x_2280_ = lean_st_ref_take(v___y_2272_);
v_traceState_2281_ = lean_ctor_get(v___x_2280_, 4);
v_env_2282_ = lean_ctor_get(v___x_2280_, 0);
v_nextMacroScope_2283_ = lean_ctor_get(v___x_2280_, 1);
v_ngen_2284_ = lean_ctor_get(v___x_2280_, 2);
v_auxDeclNGen_2285_ = lean_ctor_get(v___x_2280_, 3);
v_cache_2286_ = lean_ctor_get(v___x_2280_, 5);
v_messages_2287_ = lean_ctor_get(v___x_2280_, 6);
v_infoState_2288_ = lean_ctor_get(v___x_2280_, 7);
v_snapshotTasks_2289_ = lean_ctor_get(v___x_2280_, 8);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2291_ = v___x_2280_;
v_isShared_2292_ = v_isSharedCheck_2319_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_snapshotTasks_2289_);
lean_inc(v_infoState_2288_);
lean_inc(v_messages_2287_);
lean_inc(v_cache_2286_);
lean_inc(v_traceState_2281_);
lean_inc(v_auxDeclNGen_2285_);
lean_inc(v_ngen_2284_);
lean_inc(v_nextMacroScope_2283_);
lean_inc(v_env_2282_);
lean_dec(v___x_2280_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2319_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
uint64_t v_tid_2293_; lean_object* v_traces_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2318_; 
v_tid_2293_ = lean_ctor_get_uint64(v_traceState_2281_, sizeof(void*)*1);
v_traces_2294_ = lean_ctor_get(v_traceState_2281_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_traceState_2281_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2296_ = v_traceState_2281_;
v_isShared_2297_ = v_isSharedCheck_2318_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_traces_2294_);
lean_dec(v_traceState_2281_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2318_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; double v___x_2299_; uint8_t v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2298_ = lean_box(0);
v___x_2299_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_2300_ = 0;
v___x_2301_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_2302_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2302_, 0, v_cls_2267_);
lean_ctor_set(v___x_2302_, 1, v___x_2298_);
lean_ctor_set(v___x_2302_, 2, v___x_2301_);
lean_ctor_set_float(v___x_2302_, sizeof(void*)*3, v___x_2299_);
lean_ctor_set_float(v___x_2302_, sizeof(void*)*3 + 8, v___x_2299_);
lean_ctor_set_uint8(v___x_2302_, sizeof(void*)*3 + 16, v___x_2300_);
v___x_2303_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_2304_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2302_);
lean_ctor_set(v___x_2304_, 1, v_a_2276_);
lean_ctor_set(v___x_2304_, 2, v___x_2303_);
lean_inc(v_ref_2274_);
v___x_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2305_, 0, v_ref_2274_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = l_Lean_PersistentArray_push___redArg(v_traces_2294_, v___x_2305_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2306_);
v___x_2308_ = v___x_2296_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2306_);
lean_ctor_set_uint64(v_reuseFailAlloc_2317_, sizeof(void*)*1, v_tid_2293_);
v___x_2308_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v___x_2308_);
v___x_2310_ = v___x_2291_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_env_2282_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_nextMacroScope_2283_);
lean_ctor_set(v_reuseFailAlloc_2316_, 2, v_ngen_2284_);
lean_ctor_set(v_reuseFailAlloc_2316_, 3, v_auxDeclNGen_2285_);
lean_ctor_set(v_reuseFailAlloc_2316_, 4, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2316_, 5, v_cache_2286_);
lean_ctor_set(v_reuseFailAlloc_2316_, 6, v_messages_2287_);
lean_ctor_set(v_reuseFailAlloc_2316_, 7, v_infoState_2288_);
lean_ctor_set(v_reuseFailAlloc_2316_, 8, v_snapshotTasks_2289_);
v___x_2310_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2311_ = lean_st_ref_set(v___y_2272_, v___x_2310_);
v___x_2312_ = lean_box(0);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 0, v___x_2312_);
v___x_2314_ = v___x_2278_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2321_, lean_object* v_msg_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2321_, v_msg_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
return v_res_2328_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__0));
v___x_2331_ = l_Lean_stringToMessageData(v___x_2330_);
return v___x_2331_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__2));
v___x_2334_ = l_Lean_stringToMessageData(v___x_2333_);
return v___x_2334_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__4));
v___x_2337_ = l_Lean_stringToMessageData(v___x_2336_);
return v___x_2337_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2338_ = lean_box(0);
v___x_2339_ = lean_unsigned_to_nat(16u);
v___x_2340_ = lean_mk_array(v___x_2339_, v___x_2338_);
return v___x_2340_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7(void){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2341_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__6);
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v___x_2341_);
return v___x_2343_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__9));
v___x_2348_ = l_Lean_stringToMessageData(v___x_2347_);
return v___x_2348_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__11));
v___x_2351_ = l_Lean_stringToMessageData(v___x_2350_);
return v___x_2351_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__13));
v___x_2354_ = l_Lean_stringToMessageData(v___x_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object* v_lhs_2355_, lean_object* v_rhs_2356_, uint8_t v___x_2357_, lean_object* v___f_2358_, lean_object* v_cls_2359_, lean_object* v_P_2360_, lean_object* v_____r_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2381_; 
lean_inc_ref(v_lhs_2355_);
v___x_2381_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2355_);
if (lean_obj_tag(v___x_2381_) == 1)
{
lean_object* v_val_2382_; lean_object* v___x_2383_; 
v_val_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_val_2382_);
lean_dec_ref_known(v___x_2381_, 1);
lean_inc_ref(v_rhs_2356_);
v___x_2383_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2356_);
if (lean_obj_tag(v___x_2383_) == 1)
{
lean_object* v_val_2384_; uint8_t v___x_2423_; 
v_val_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_val_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v___x_2423_ = lean_expr_eqv(v_val_2382_, v_val_2384_);
if (v___x_2423_ == 0)
{
lean_dec_ref(v_P_2360_);
goto v___jp_2385_;
}
else
{
if (v___x_2357_ == 0)
{
lean_object* v_options_2424_; lean_object* v_inheritedTraceOptions_2425_; uint8_t v_hasTrace_2426_; lean_object* v___x_2427_; lean_object* v___f_2428_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; 
lean_dec(v_val_2384_);
lean_dec_ref(v___f_2358_);
v_options_2424_ = lean_ctor_get(v___y_2369_, 2);
v_inheritedTraceOptions_2425_ = lean_ctor_get(v___y_2369_, 13);
v_hasTrace_2426_ = lean_ctor_get_uint8(v_options_2424_, sizeof(void*)*1);
v___x_2427_ = lean_box(v___x_2357_);
lean_inc(v_val_2382_);
v___f_2428_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed), 13, 5);
lean_closure_set(v___f_2428_, 0, v_val_2382_);
lean_closure_set(v___f_2428_, 1, v_lhs_2355_);
lean_closure_set(v___f_2428_, 2, v_rhs_2356_);
lean_closure_set(v___f_2428_, 3, v_P_2360_);
lean_closure_set(v___f_2428_, 4, v___x_2427_);
if (v_hasTrace_2426_ == 0)
{
lean_dec(v_cls_2359_);
v___y_2430_ = v___y_2365_;
v___y_2431_ = v___y_2366_;
v___y_2432_ = v___y_2367_;
v___y_2433_ = v___y_2368_;
v___y_2434_ = v___y_2369_;
v___y_2435_ = v___y_2370_;
goto v___jp_2429_;
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2441_; uint8_t v___x_2442_; 
v___x_2440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2359_);
v___x_2441_ = l_Lean_Name_append(v___x_2440_, v_cls_2359_);
v___x_2442_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2425_, v_options_2424_, v___x_2441_);
lean_dec(v___x_2441_);
if (v___x_2442_ == 0)
{
lean_dec(v_cls_2359_);
v___y_2430_ = v___y_2365_;
v___y_2431_ = v___y_2366_;
v___y_2432_ = v___y_2367_;
v___y_2433_ = v___y_2368_;
v___y_2434_ = v___y_2369_;
v___y_2435_ = v___y_2370_;
goto v___jp_2429_;
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2443_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10);
lean_inc(v_val_2382_);
v___x_2444_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2382_);
v___x_2445_ = l_Lean_MessageData_ofExpr(v___x_2444_);
v___x_2446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2443_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12);
v___x_2448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2359_, v___x_2448_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_dec_ref_known(v___x_2449_, 1);
v___y_2430_ = v___y_2365_;
v___y_2431_ = v___y_2366_;
v___y_2432_ = v___y_2367_;
v___y_2433_ = v___y_2368_;
v___y_2434_ = v___y_2369_;
v___y_2435_ = v___y_2370_;
goto v___jp_2429_;
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec_ref(v___f_2428_);
lean_dec(v_val_2382_);
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
v___jp_2429_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2436_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7);
v___x_2437_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8));
v___x_2438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2438_, 0, v_val_2382_);
lean_ctor_set(v___x_2438_, 1, v___x_2436_);
lean_ctor_set(v___x_2438_, 2, v___x_2437_);
v___x_2439_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2428_, v___x_2438_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_);
return v___x_2439_;
}
}
else
{
lean_dec_ref(v_P_2360_);
goto v___jp_2385_;
}
}
v___jp_2385_:
{
lean_object* v_inheritedTraceOptions_2386_; lean_object* v___x_2387_; 
v_inheritedTraceOptions_2386_ = lean_ctor_get(v___y_2369_, 13);
lean_inc(v___y_2370_);
lean_inc_ref(v___y_2369_);
lean_inc(v___y_2368_);
lean_inc_ref(v___y_2367_);
lean_inc(v___y_2366_);
lean_inc_ref(v___y_2365_);
lean_inc(v___y_2364_);
lean_inc_ref(v___y_2363_);
lean_inc(v___y_2362_);
lean_inc_ref(v_inheritedTraceOptions_2386_);
v___x_2387_ = lean_apply_11(v___f_2358_, v_inheritedTraceOptions_2386_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, lean_box(0));
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; uint8_t v___x_2389_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v___x_2389_ = lean_unbox(v_a_2388_);
lean_dec(v_a_2388_);
if (v___x_2389_ == 0)
{
lean_dec(v_val_2384_);
lean_dec(v_val_2382_);
lean_dec(v_cls_2359_);
lean_dec_ref(v_rhs_2356_);
lean_dec_ref(v_lhs_2355_);
goto v___jp_2372_;
}
else
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2390_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1);
v___x_2391_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2382_);
v___x_2392_ = l_Lean_MessageData_ofExpr(v___x_2391_);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2390_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3);
v___x_2395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2393_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = l_Lean_indentExpr(v_lhs_2355_);
v___x_2397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2384_);
v___x_2401_ = l_Lean_MessageData_ofExpr(v___x_2400_);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2399_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v___x_2394_);
v___x_2404_ = l_Lean_indentExpr(v_rhs_2356_);
v___x_2405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2403_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2359_, v___x_2405_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_dec_ref_known(v___x_2406_, 1);
goto v___jp_2372_;
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v_val_2384_);
lean_dec(v_val_2382_);
lean_dec(v_cls_2359_);
lean_dec_ref(v_rhs_2356_);
lean_dec_ref(v_lhs_2355_);
v_a_2415_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2387_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2387_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2458_; lean_object* v___x_2459_; 
lean_dec(v___x_2383_);
lean_dec(v_val_2382_);
lean_dec_ref(v_P_2360_);
lean_dec_ref(v_lhs_2355_);
v_inheritedTraceOptions_2458_ = lean_ctor_get(v___y_2369_, 13);
lean_inc(v___y_2370_);
lean_inc_ref(v___y_2369_);
lean_inc(v___y_2368_);
lean_inc_ref(v___y_2367_);
lean_inc(v___y_2366_);
lean_inc_ref(v___y_2365_);
lean_inc(v___y_2364_);
lean_inc_ref(v___y_2363_);
lean_inc(v___y_2362_);
lean_inc_ref(v_inheritedTraceOptions_2458_);
v___x_2459_ = lean_apply_11(v___f_2358_, v_inheritedTraceOptions_2458_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, lean_box(0));
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; uint8_t v___x_2461_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v___x_2461_ = lean_unbox(v_a_2460_);
lean_dec(v_a_2460_);
if (v___x_2461_ == 0)
{
lean_dec(v_cls_2359_);
lean_dec_ref(v_rhs_2356_);
goto v___jp_2375_;
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2462_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14);
v___x_2463_ = l_Lean_indentExpr(v_rhs_2356_);
v___x_2464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2462_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2359_, v___x_2464_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_dec_ref_known(v___x_2465_, 1);
goto v___jp_2375_;
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v_cls_2359_);
lean_dec_ref(v_rhs_2356_);
v_a_2474_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2459_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2459_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2482_; lean_object* v___x_2483_; 
lean_dec(v___x_2381_);
lean_dec_ref(v_P_2360_);
lean_dec_ref(v_rhs_2356_);
v_inheritedTraceOptions_2482_ = lean_ctor_get(v___y_2369_, 13);
lean_inc(v___y_2370_);
lean_inc_ref(v___y_2369_);
lean_inc(v___y_2368_);
lean_inc_ref(v___y_2367_);
lean_inc(v___y_2366_);
lean_inc_ref(v___y_2365_);
lean_inc(v___y_2364_);
lean_inc_ref(v___y_2363_);
lean_inc(v___y_2362_);
lean_inc_ref(v_inheritedTraceOptions_2482_);
v___x_2483_ = lean_apply_11(v___f_2358_, v_inheritedTraceOptions_2482_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, lean_box(0));
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; uint8_t v___x_2485_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v___x_2485_ = lean_unbox(v_a_2484_);
lean_dec(v_a_2484_);
if (v___x_2485_ == 0)
{
lean_dec(v_cls_2359_);
lean_dec_ref(v_lhs_2355_);
goto v___jp_2378_;
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2486_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14);
v___x_2487_ = l_Lean_indentExpr(v_lhs_2355_);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2359_, v___x_2488_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_dec_ref_known(v___x_2489_, 1);
goto v___jp_2378_;
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2489_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2489_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec(v_cls_2359_);
lean_dec_ref(v_lhs_2355_);
v_a_2498_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2483_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2483_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
v___jp_2372_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2373_, 0, v___x_2357_);
lean_ctor_set_uint8(v___x_2373_, 1, v___x_2357_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
v___jp_2375_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2376_, 0, v___x_2357_);
lean_ctor_set_uint8(v___x_2376_, 1, v___x_2357_);
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
return v___x_2377_;
}
v___jp_2378_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2379_, 0, v___x_2357_);
lean_ctor_set_uint8(v___x_2379_, 1, v___x_2357_);
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
return v___x_2380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object** _args){
lean_object* v_lhs_2506_ = _args[0];
lean_object* v_rhs_2507_ = _args[1];
lean_object* v___x_2508_ = _args[2];
lean_object* v___f_2509_ = _args[3];
lean_object* v_cls_2510_ = _args[4];
lean_object* v_P_2511_ = _args[5];
lean_object* v_____r_2512_ = _args[6];
lean_object* v___y_2513_ = _args[7];
lean_object* v___y_2514_ = _args[8];
lean_object* v___y_2515_ = _args[9];
lean_object* v___y_2516_ = _args[10];
lean_object* v___y_2517_ = _args[11];
lean_object* v___y_2518_ = _args[12];
lean_object* v___y_2519_ = _args[13];
lean_object* v___y_2520_ = _args[14];
lean_object* v___y_2521_ = _args[15];
lean_object* v___y_2522_ = _args[16];
_start:
{
uint8_t v___x_210630__boxed_2523_; lean_object* v_res_2524_; 
v___x_210630__boxed_2523_ = lean_unbox(v___x_2508_);
v_res_2524_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2506_, v_rhs_2507_, v___x_210630__boxed_2523_, v___f_2509_, v_cls_2510_, v_P_2511_, v_____r_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(lean_object* v_val_2525_, lean_object* v_lhs_2526_, lean_object* v_rhs_2527_, lean_object* v_P_2528_, uint8_t v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v___x_2538_; 
lean_inc_ref(v_lhs_2526_);
lean_inc_ref(v_val_2525_);
v___x_2538_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2525_, v_lhs_2526_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v_fst_2540_; lean_object* v_snd_2541_; lean_object* v___x_2542_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
v_fst_2540_ = lean_ctor_get(v_a_2539_, 0);
lean_inc(v_fst_2540_);
v_snd_2541_ = lean_ctor_get(v_a_2539_, 1);
lean_inc(v_snd_2541_);
lean_dec(v_a_2539_);
lean_inc_ref(v_rhs_2527_);
lean_inc_ref(v_val_2525_);
v___x_2542_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2525_, v_rhs_2527_, v_snd_2541_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v_fst_2544_; lean_object* v_snd_2545_; lean_object* v___x_2546_; lean_object* v_a_2547_; lean_object* v_fst_2548_; lean_object* v_snd_2549_; lean_object* v_common_2550_; lean_object* v_x_2551_; lean_object* v_y_2552_; lean_object* v___x_2553_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v___x_2542_, 1);
v_fst_2544_ = lean_ctor_get(v_a_2543_, 0);
lean_inc(v_fst_2544_);
v_snd_2545_ = lean_ctor_get(v_a_2543_, 1);
lean_inc(v_snd_2545_);
lean_dec(v_a_2543_);
v___x_2546_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_2540_, v_fst_2544_, v_snd_2545_);
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref(v___x_2546_);
v_fst_2548_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_fst_2548_);
v_snd_2549_ = lean_ctor_get(v_a_2547_, 1);
lean_inc(v_snd_2549_);
lean_dec(v_a_2547_);
v_common_2550_ = lean_ctor_get(v_fst_2548_, 0);
lean_inc_ref(v_common_2550_);
v_x_2551_ = lean_ctor_get(v_fst_2548_, 1);
lean_inc_ref(v_x_2551_);
v_y_2552_ = lean_ctor_get(v_fst_2548_, 2);
lean_inc_ref(v_y_2552_);
lean_dec(v_fst_2548_);
lean_inc_ref(v_val_2525_);
v___x_2553_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_2550_, v_val_2525_, v_snd_2549_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec_ref(v_common_2550_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v_fst_2555_; lean_object* v_snd_2556_; lean_object* v___x_2557_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v_fst_2555_ = lean_ctor_get(v_a_2554_, 0);
lean_inc(v_fst_2555_);
v_snd_2556_ = lean_ctor_get(v_a_2554_, 1);
lean_inc(v_snd_2556_);
lean_dec(v_a_2554_);
lean_inc_ref(v_val_2525_);
v___x_2557_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_2551_, v_val_2525_, v_snd_2556_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec_ref(v_x_2551_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v_fst_2559_; lean_object* v_snd_2560_; lean_object* v___x_2561_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2557_, 1);
v_fst_2559_ = lean_ctor_get(v_a_2558_, 0);
lean_inc(v_fst_2559_);
v_snd_2560_ = lean_ctor_get(v_a_2558_, 1);
lean_inc(v_snd_2560_);
lean_dec(v_a_2558_);
lean_inc_ref(v_val_2525_);
v___x_2561_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_2552_, v_val_2525_, v_snd_2560_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec_ref(v_y_2552_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2626_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2626_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2626_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v_fst_2566_; lean_object* v_snd_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2625_; 
v_fst_2566_ = lean_ctor_get(v_a_2562_, 0);
v_snd_2567_ = lean_ctor_get(v_a_2562_, 1);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_a_2562_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2569_ = v_a_2562_;
v_isShared_2570_ = v_isSharedCheck_2625_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_snd_2567_);
lean_inc(v_fst_2566_);
lean_dec(v_a_2562_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2625_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___x_2615_; lean_object* v___f_2616_; lean_object* v___y_2618_; lean_object* v___x_2622_; 
lean_inc_ref(v_val_2525_);
v___x_2615_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2525_);
v___f_2616_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2616_, 0, v___x_2615_);
lean_inc(v_fst_2555_);
lean_inc_ref(v___f_2616_);
v___x_2622_ = l_Option_merge___redArg(v___f_2616_, v_fst_2555_, v_fst_2559_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v___x_2623_; 
lean_inc_ref(v_val_2525_);
v___x_2623_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2525_);
v___y_2618_ = v___x_2623_;
goto v___jp_2617_;
}
else
{
lean_object* v_val_2624_; 
v_val_2624_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_val_2624_);
lean_dec_ref_known(v___x_2622_, 1);
v___y_2618_ = v_val_2624_;
goto v___jp_2617_;
}
v___jp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
lean_inc_ref(v_P_2528_);
v___x_2574_ = l_Lean_mkAppB(v_P_2528_, v_lhs_2526_, v_rhs_2527_);
v___x_2575_ = l_Lean_mkAppB(v_P_2528_, v___y_2572_, v___y_2573_);
v___x_2576_ = lean_expr_eqv(v___x_2574_, v___x_2575_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; 
lean_del_object(v___x_2564_);
lean_inc_ref(v___x_2575_);
v___x_2577_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_2574_, v___x_2575_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2579_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref_known(v___x_2577_, 1);
v___x_2579_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2575_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2591_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2591_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2591_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2584_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2584_, 0, v_a_2580_);
lean_ctor_set(v___x_2584_, 1, v_a_2578_);
lean_ctor_set_uint8(v___x_2584_, sizeof(void*)*2, v___x_2576_);
lean_ctor_set_uint8(v___x_2584_, sizeof(void*)*2 + 1, v___x_2576_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2584_);
v___x_2586_ = v___x_2569_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_snd_2567_);
v___x_2586_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2588_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 0, v___x_2586_);
v___x_2588_ = v___x_2582_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_a_2578_);
lean_del_object(v___x_2569_);
lean_dec(v_snd_2567_);
v_a_2592_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2579_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2579_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec_ref(v___x_2575_);
lean_del_object(v___x_2569_);
lean_dec(v_snd_2567_);
v_a_2600_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2577_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2577_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
lean_dec_ref(v___x_2575_);
lean_dec_ref(v___x_2574_);
v___x_2608_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2608_, 0, v___y_2529_);
lean_ctor_set_uint8(v___x_2608_, 1, v___y_2529_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2608_);
v___x_2610_ = v___x_2569_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_snd_2567_);
v___x_2610_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2612_; 
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2610_);
v___x_2612_ = v___x_2564_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
v___jp_2617_:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Option_merge___redArg(v___f_2616_, v_fst_2555_, v_fst_2566_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2525_);
v___y_2572_ = v___y_2618_;
v___y_2573_ = v___x_2620_;
goto v___jp_2571_;
}
else
{
lean_object* v_val_2621_; 
lean_dec_ref(v_val_2525_);
v_val_2621_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_val_2621_);
lean_dec_ref_known(v___x_2619_, 1);
v___y_2572_ = v___y_2618_;
v___y_2573_ = v_val_2621_;
goto v___jp_2571_;
}
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v_fst_2559_);
lean_dec(v_fst_2555_);
lean_dec_ref(v_P_2528_);
lean_dec_ref(v_rhs_2527_);
lean_dec_ref(v_lhs_2526_);
lean_dec_ref(v_val_2525_);
v_a_2627_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2561_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2561_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v_fst_2555_);
lean_dec_ref(v_y_2552_);
lean_dec_ref(v_P_2528_);
lean_dec_ref(v_rhs_2527_);
lean_dec_ref(v_lhs_2526_);
lean_dec_ref(v_val_2525_);
v_a_2635_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2557_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2557_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v_y_2552_);
lean_dec_ref(v_x_2551_);
lean_dec_ref(v_P_2528_);
lean_dec_ref(v_rhs_2527_);
lean_dec_ref(v_lhs_2526_);
lean_dec_ref(v_val_2525_);
v_a_2643_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2553_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2553_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v_fst_2540_);
lean_dec_ref(v_P_2528_);
lean_dec_ref(v_rhs_2527_);
lean_dec_ref(v_lhs_2526_);
lean_dec_ref(v_val_2525_);
v_a_2651_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2542_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2542_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec_ref(v_P_2528_);
lean_dec_ref(v_rhs_2527_);
lean_dec_ref(v_lhs_2526_);
lean_dec_ref(v_val_2525_);
v_a_2659_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2538_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2538_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7___boxed(lean_object* v_val_2667_, lean_object* v_lhs_2668_, lean_object* v_rhs_2669_, lean_object* v_P_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
uint8_t v___y_210959__boxed_2680_; lean_object* v_res_2681_; 
v___y_210959__boxed_2680_ = lean_unbox(v___y_2671_);
v_res_2681_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(v_val_2667_, v_lhs_2668_, v_rhs_2669_, v_P_2670_, v___y_210959__boxed_2680_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object* v_lhs_2682_, lean_object* v_rhs_2683_, lean_object* v_P_2684_, lean_object* v_cls_2685_, uint8_t v___x_2686_, lean_object* v___f_2687_, uint8_t v___x_2688_, lean_object* v_____r_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___x_2706_; 
lean_inc_ref(v_lhs_2682_);
v___x_2706_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2682_);
if (lean_obj_tag(v___x_2706_) == 1)
{
lean_object* v_val_2707_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; uint8_t v___y_2721_; lean_object* v___x_2745_; 
v_val_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_val_2707_);
lean_dec_ref_known(v___x_2706_, 1);
lean_inc_ref(v_rhs_2683_);
v___x_2745_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2683_);
if (lean_obj_tag(v___x_2745_) == 1)
{
lean_object* v_val_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2793_; 
v_val_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2793_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_val_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2793_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
uint8_t v___x_2750_; 
v___x_2750_ = lean_expr_eqv(v_val_2707_, v_val_2746_);
if (v___x_2750_ == 0)
{
if (v___x_2686_ == 0)
{
lean_del_object(v___x_2748_);
lean_dec(v_val_2746_);
lean_dec_ref(v___f_2687_);
v___y_2721_ = v___x_2686_;
goto v___jp_2720_;
}
else
{
lean_object* v_inheritedTraceOptions_2756_; lean_object* v___x_2757_; 
lean_dec_ref(v_P_2684_);
v_inheritedTraceOptions_2756_ = lean_ctor_get(v___y_2697_, 13);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___y_2696_);
lean_inc_ref(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
lean_inc(v___y_2690_);
lean_inc_ref(v_inheritedTraceOptions_2756_);
v___x_2757_ = lean_apply_11(v___f_2687_, v_inheritedTraceOptions_2756_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, lean_box(0));
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; uint8_t v___x_2759_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref_known(v___x_2757_, 1);
v___x_2759_ = lean_unbox(v_a_2758_);
lean_dec(v_a_2758_);
if (v___x_2759_ == 0)
{
lean_dec(v_val_2746_);
lean_dec(v_val_2707_);
lean_dec(v_cls_2685_);
lean_dec_ref(v_rhs_2683_);
lean_dec_ref(v_lhs_2682_);
goto v___jp_2751_;
}
else
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2760_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1);
v___x_2761_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2707_);
v___x_2762_ = l_Lean_MessageData_ofExpr(v___x_2761_);
v___x_2763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2760_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3);
v___x_2765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = l_Lean_indentExpr(v_lhs_2682_);
v___x_2767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5);
v___x_2769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2767_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2746_);
v___x_2771_ = l_Lean_MessageData_ofExpr(v___x_2770_);
v___x_2772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2769_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
v___x_2773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
lean_ctor_set(v___x_2773_, 1, v___x_2764_);
v___x_2774_ = l_Lean_indentExpr(v_rhs_2683_);
v___x_2775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2773_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
v___x_2776_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2685_, v___x_2775_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_dec_ref_known(v___x_2776_, 1);
goto v___jp_2751_;
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_del_object(v___x_2748_);
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_del_object(v___x_2748_);
lean_dec(v_val_2746_);
lean_dec(v_val_2707_);
lean_dec(v_cls_2685_);
lean_dec_ref(v_rhs_2683_);
lean_dec_ref(v_lhs_2682_);
v_a_2785_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2757_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2757_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
else
{
lean_del_object(v___x_2748_);
lean_dec(v_val_2746_);
lean_dec_ref(v___f_2687_);
v___y_2721_ = v___x_2688_;
goto v___jp_2720_;
}
v___jp_2751_:
{
lean_object* v___x_2752_; lean_object* v___x_2754_; 
v___x_2752_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2752_, 0, v___x_2750_);
lean_ctor_set_uint8(v___x_2752_, 1, v___x_2750_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set_tag(v___x_2748_, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2752_);
v___x_2754_ = v___x_2748_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2794_; lean_object* v___x_2795_; 
lean_dec(v___x_2745_);
lean_dec(v_val_2707_);
lean_dec_ref(v_P_2684_);
lean_dec_ref(v_lhs_2682_);
v_inheritedTraceOptions_2794_ = lean_ctor_get(v___y_2697_, 13);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___y_2696_);
lean_inc_ref(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
lean_inc(v___y_2690_);
lean_inc_ref(v_inheritedTraceOptions_2794_);
v___x_2795_ = lean_apply_11(v___f_2687_, v_inheritedTraceOptions_2794_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, lean_box(0));
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; uint8_t v___x_2797_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2795_, 1);
v___x_2797_ = lean_unbox(v_a_2796_);
lean_dec(v_a_2796_);
if (v___x_2797_ == 0)
{
lean_dec(v_cls_2685_);
lean_dec_ref(v_rhs_2683_);
goto v___jp_2700_;
}
else
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2798_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14);
v___x_2799_ = l_Lean_indentExpr(v_rhs_2683_);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2685_, v___x_2800_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_dec_ref_known(v___x_2801_, 1);
goto v___jp_2700_;
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_cls_2685_);
lean_dec_ref(v_rhs_2683_);
v_a_2810_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2795_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2795_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
v___jp_2708_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2716_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7);
v___x_2717_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8));
v___x_2718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2718_, 0, v_val_2707_);
lean_ctor_set(v___x_2718_, 1, v___x_2716_);
lean_ctor_set(v___x_2718_, 2, v___x_2717_);
v___x_2719_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2709_, v___x_2718_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
return v___x_2719_;
}
v___jp_2720_:
{
lean_object* v_options_2722_; lean_object* v_inheritedTraceOptions_2723_; uint8_t v_hasTrace_2724_; lean_object* v___x_2725_; lean_object* v___f_2726_; 
v_options_2722_ = lean_ctor_get(v___y_2697_, 2);
v_inheritedTraceOptions_2723_ = lean_ctor_get(v___y_2697_, 13);
v_hasTrace_2724_ = lean_ctor_get_uint8(v_options_2722_, sizeof(void*)*1);
v___x_2725_ = lean_box(v___y_2721_);
lean_inc(v_val_2707_);
v___f_2726_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7___boxed), 13, 5);
lean_closure_set(v___f_2726_, 0, v_val_2707_);
lean_closure_set(v___f_2726_, 1, v_lhs_2682_);
lean_closure_set(v___f_2726_, 2, v_rhs_2683_);
lean_closure_set(v___f_2726_, 3, v_P_2684_);
lean_closure_set(v___f_2726_, 4, v___x_2725_);
if (v_hasTrace_2724_ == 0)
{
lean_dec(v_cls_2685_);
v___y_2709_ = v___f_2726_;
v___y_2710_ = v___y_2693_;
v___y_2711_ = v___y_2694_;
v___y_2712_ = v___y_2695_;
v___y_2713_ = v___y_2696_;
v___y_2714_ = v___y_2697_;
v___y_2715_ = v___y_2698_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_2727_; lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2685_);
v___x_2728_ = l_Lean_Name_append(v___x_2727_, v_cls_2685_);
v___x_2729_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2723_, v_options_2722_, v___x_2728_);
lean_dec(v___x_2728_);
if (v___x_2729_ == 0)
{
lean_dec(v_cls_2685_);
v___y_2709_ = v___f_2726_;
v___y_2710_ = v___y_2693_;
v___y_2711_ = v___y_2694_;
v___y_2712_ = v___y_2695_;
v___y_2713_ = v___y_2696_;
v___y_2714_ = v___y_2697_;
v___y_2715_ = v___y_2698_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2730_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10);
lean_inc(v_val_2707_);
v___x_2731_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2707_);
v___x_2732_ = l_Lean_MessageData_ofExpr(v___x_2731_);
v___x_2733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2730_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
v___x_2734_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12);
v___x_2735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v___x_2736_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2685_, v___x_2735_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_dec_ref_known(v___x_2736_, 1);
v___y_2709_ = v___f_2726_;
v___y_2710_ = v___y_2693_;
v___y_2711_ = v___y_2694_;
v___y_2712_ = v___y_2695_;
v___y_2713_ = v___y_2696_;
v___y_2714_ = v___y_2697_;
v___y_2715_ = v___y_2698_;
goto v___jp_2708_;
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v___f_2726_);
lean_dec(v_val_2707_);
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2818_; lean_object* v___x_2819_; 
lean_dec(v___x_2706_);
lean_dec_ref(v_P_2684_);
lean_dec_ref(v_rhs_2683_);
v_inheritedTraceOptions_2818_ = lean_ctor_get(v___y_2697_, 13);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v___y_2696_);
lean_inc_ref(v___y_2695_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
lean_inc(v___y_2690_);
lean_inc_ref(v_inheritedTraceOptions_2818_);
v___x_2819_ = lean_apply_11(v___f_2687_, v_inheritedTraceOptions_2818_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, lean_box(0));
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; uint8_t v___x_2821_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2821_ = lean_unbox(v_a_2820_);
lean_dec(v_a_2820_);
if (v___x_2821_ == 0)
{
lean_dec(v_cls_2685_);
lean_dec_ref(v_lhs_2682_);
goto v___jp_2703_;
}
else
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2822_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14);
v___x_2823_ = l_Lean_indentExpr(v_lhs_2682_);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2685_, v___x_2824_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_dec_ref_known(v___x_2825_, 1);
goto v___jp_2703_;
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_cls_2685_);
lean_dec_ref(v_lhs_2682_);
v_a_2834_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2819_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2819_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
v___jp_2700_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2701_, 0, v___x_2688_);
lean_ctor_set_uint8(v___x_2701_, 1, v___x_2688_);
v___x_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
return v___x_2702_;
}
v___jp_2703_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2704_, 0, v___x_2688_);
lean_ctor_set_uint8(v___x_2704_, 1, v___x_2688_);
v___x_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
return v___x_2705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object** _args){
lean_object* v_lhs_2842_ = _args[0];
lean_object* v_rhs_2843_ = _args[1];
lean_object* v_P_2844_ = _args[2];
lean_object* v_cls_2845_ = _args[3];
lean_object* v___x_2846_ = _args[4];
lean_object* v___f_2847_ = _args[5];
lean_object* v___x_2848_ = _args[6];
lean_object* v_____r_2849_ = _args[7];
lean_object* v___y_2850_ = _args[8];
lean_object* v___y_2851_ = _args[9];
lean_object* v___y_2852_ = _args[10];
lean_object* v___y_2853_ = _args[11];
lean_object* v___y_2854_ = _args[12];
lean_object* v___y_2855_ = _args[13];
lean_object* v___y_2856_ = _args[14];
lean_object* v___y_2857_ = _args[15];
lean_object* v___y_2858_ = _args[16];
lean_object* v___y_2859_ = _args[17];
_start:
{
uint8_t v___x_211281__boxed_2860_; uint8_t v___x_211283__boxed_2861_; lean_object* v_res_2862_; 
v___x_211281__boxed_2860_ = lean_unbox(v___x_2846_);
v___x_211283__boxed_2861_ = lean_unbox(v___x_2848_);
v_res_2862_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2842_, v_rhs_2843_, v_P_2844_, v_cls_2845_, v___x_211281__boxed_2860_, v___f_2847_, v___x_211283__boxed_2861_, v_____r_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
return v_res_2862_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_e_2863_){
_start:
{
if (lean_obj_tag(v_e_2863_) == 0)
{
uint8_t v___x_2864_; 
v___x_2864_ = 2;
return v___x_2864_;
}
else
{
uint8_t v___x_2865_; 
v___x_2865_ = 0;
return v___x_2865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_e_2866_){
_start:
{
uint8_t v_res_2867_; lean_object* v_r_2868_; 
v_res_2867_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_e_2866_);
lean_dec_ref(v_e_2866_);
v_r_2868_ = lean_box(v_res_2867_);
return v_r_2868_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_x_2869_){
_start:
{
if (lean_obj_tag(v_x_2869_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
v_a_2871_ = lean_ctor_get(v_x_2869_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_x_2869_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v_x_2869_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v_x_2869_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
lean_ctor_set_tag(v___x_2873_, 1);
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
v_a_2879_ = lean_ctor_get(v_x_2869_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v_x_2869_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v_x_2869_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v_x_2869_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
lean_ctor_set_tag(v___x_2881_, 0);
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_x_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_2887_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2890_, lean_object* v_opt_2891_){
_start:
{
lean_object* v_name_2892_; lean_object* v_defValue_2893_; lean_object* v_map_2894_; lean_object* v___x_2895_; 
v_name_2892_ = lean_ctor_get(v_opt_2891_, 0);
v_defValue_2893_ = lean_ctor_get(v_opt_2891_, 1);
v_map_2894_ = lean_ctor_get(v_opts_2890_, 0);
v___x_2895_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2894_, v_name_2892_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_inc(v_defValue_2893_);
return v_defValue_2893_;
}
else
{
lean_object* v_val_2896_; 
v_val_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_val_2896_);
lean_dec_ref_known(v___x_2895_, 1);
if (lean_obj_tag(v_val_2896_) == 3)
{
lean_object* v_v_2897_; 
v_v_2897_ = lean_ctor_get(v_val_2896_, 0);
lean_inc(v_v_2897_);
lean_dec_ref_known(v_val_2896_, 1);
return v_v_2897_;
}
else
{
lean_dec(v_val_2896_);
lean_inc(v_defValue_2893_);
return v_defValue_2893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2898_, lean_object* v_opt_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2898_, v_opt_2899_);
lean_dec_ref(v_opt_2899_);
lean_dec_ref(v_opts_2898_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t v_sz_2901_, size_t v_i_2902_, lean_object* v_bs_2903_){
_start:
{
uint8_t v___x_2904_; 
v___x_2904_ = lean_usize_dec_lt(v_i_2902_, v_sz_2901_);
if (v___x_2904_ == 0)
{
return v_bs_2903_;
}
else
{
lean_object* v_v_2905_; lean_object* v_msg_2906_; lean_object* v___x_2907_; lean_object* v_bs_x27_2908_; size_t v___x_2909_; size_t v___x_2910_; lean_object* v___x_2911_; 
v_v_2905_ = lean_array_uget_borrowed(v_bs_2903_, v_i_2902_);
v_msg_2906_ = lean_ctor_get(v_v_2905_, 1);
lean_inc_ref(v_msg_2906_);
v___x_2907_ = lean_unsigned_to_nat(0u);
v_bs_x27_2908_ = lean_array_uset(v_bs_2903_, v_i_2902_, v___x_2907_);
v___x_2909_ = ((size_t)1ULL);
v___x_2910_ = lean_usize_add(v_i_2902_, v___x_2909_);
v___x_2911_ = lean_array_uset(v_bs_x27_2908_, v_i_2902_, v_msg_2906_);
v_i_2902_ = v___x_2910_;
v_bs_2903_ = v___x_2911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2913_, lean_object* v_i_2914_, lean_object* v_bs_2915_){
_start:
{
size_t v_sz_boxed_2916_; size_t v_i_boxed_2917_; lean_object* v_res_2918_; 
v_sz_boxed_2916_ = lean_unbox_usize(v_sz_2913_);
lean_dec(v_sz_2913_);
v_i_boxed_2917_ = lean_unbox_usize(v_i_2914_);
lean_dec(v_i_2914_);
v_res_2918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_boxed_2916_, v_i_boxed_2917_, v_bs_2915_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object* v_oldTraces_2919_, lean_object* v_data_2920_, lean_object* v_ref_2921_, lean_object* v_msg_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_fileName_2928_; lean_object* v_fileMap_2929_; lean_object* v_options_2930_; lean_object* v_currRecDepth_2931_; lean_object* v_maxRecDepth_2932_; lean_object* v_ref_2933_; lean_object* v_currNamespace_2934_; lean_object* v_openDecls_2935_; lean_object* v_initHeartbeats_2936_; lean_object* v_maxHeartbeats_2937_; lean_object* v_quotContext_2938_; lean_object* v_currMacroScope_2939_; uint8_t v_diag_2940_; lean_object* v_cancelTk_x3f_2941_; uint8_t v_suppressElabErrors_2942_; lean_object* v_inheritedTraceOptions_2943_; lean_object* v___x_2944_; lean_object* v_traceState_2945_; lean_object* v_traces_2946_; lean_object* v_ref_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; size_t v_sz_2950_; size_t v___x_2951_; lean_object* v___x_2952_; lean_object* v_msg_2953_; lean_object* v___x_2954_; lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2992_; 
v_fileName_2928_ = lean_ctor_get(v___y_2925_, 0);
v_fileMap_2929_ = lean_ctor_get(v___y_2925_, 1);
v_options_2930_ = lean_ctor_get(v___y_2925_, 2);
v_currRecDepth_2931_ = lean_ctor_get(v___y_2925_, 3);
v_maxRecDepth_2932_ = lean_ctor_get(v___y_2925_, 4);
v_ref_2933_ = lean_ctor_get(v___y_2925_, 5);
v_currNamespace_2934_ = lean_ctor_get(v___y_2925_, 6);
v_openDecls_2935_ = lean_ctor_get(v___y_2925_, 7);
v_initHeartbeats_2936_ = lean_ctor_get(v___y_2925_, 8);
v_maxHeartbeats_2937_ = lean_ctor_get(v___y_2925_, 9);
v_quotContext_2938_ = lean_ctor_get(v___y_2925_, 10);
v_currMacroScope_2939_ = lean_ctor_get(v___y_2925_, 11);
v_diag_2940_ = lean_ctor_get_uint8(v___y_2925_, sizeof(void*)*14);
v_cancelTk_x3f_2941_ = lean_ctor_get(v___y_2925_, 12);
v_suppressElabErrors_2942_ = lean_ctor_get_uint8(v___y_2925_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2943_ = lean_ctor_get(v___y_2925_, 13);
v___x_2944_ = lean_st_ref_get(v___y_2926_);
v_traceState_2945_ = lean_ctor_get(v___x_2944_, 4);
lean_inc_ref(v_traceState_2945_);
lean_dec(v___x_2944_);
v_traces_2946_ = lean_ctor_get(v_traceState_2945_, 0);
lean_inc_ref(v_traces_2946_);
lean_dec_ref(v_traceState_2945_);
v_ref_2947_ = l_Lean_replaceRef(v_ref_2921_, v_ref_2933_);
lean_inc_ref(v_inheritedTraceOptions_2943_);
lean_inc(v_cancelTk_x3f_2941_);
lean_inc(v_currMacroScope_2939_);
lean_inc(v_quotContext_2938_);
lean_inc(v_maxHeartbeats_2937_);
lean_inc(v_initHeartbeats_2936_);
lean_inc(v_openDecls_2935_);
lean_inc(v_currNamespace_2934_);
lean_inc(v_maxRecDepth_2932_);
lean_inc(v_currRecDepth_2931_);
lean_inc_ref(v_options_2930_);
lean_inc_ref(v_fileMap_2929_);
lean_inc_ref(v_fileName_2928_);
v___x_2948_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2948_, 0, v_fileName_2928_);
lean_ctor_set(v___x_2948_, 1, v_fileMap_2929_);
lean_ctor_set(v___x_2948_, 2, v_options_2930_);
lean_ctor_set(v___x_2948_, 3, v_currRecDepth_2931_);
lean_ctor_set(v___x_2948_, 4, v_maxRecDepth_2932_);
lean_ctor_set(v___x_2948_, 5, v_ref_2947_);
lean_ctor_set(v___x_2948_, 6, v_currNamespace_2934_);
lean_ctor_set(v___x_2948_, 7, v_openDecls_2935_);
lean_ctor_set(v___x_2948_, 8, v_initHeartbeats_2936_);
lean_ctor_set(v___x_2948_, 9, v_maxHeartbeats_2937_);
lean_ctor_set(v___x_2948_, 10, v_quotContext_2938_);
lean_ctor_set(v___x_2948_, 11, v_currMacroScope_2939_);
lean_ctor_set(v___x_2948_, 12, v_cancelTk_x3f_2941_);
lean_ctor_set(v___x_2948_, 13, v_inheritedTraceOptions_2943_);
lean_ctor_set_uint8(v___x_2948_, sizeof(void*)*14, v_diag_2940_);
lean_ctor_set_uint8(v___x_2948_, sizeof(void*)*14 + 1, v_suppressElabErrors_2942_);
v___x_2949_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2946_);
lean_dec_ref(v_traces_2946_);
v_sz_2950_ = lean_array_size(v___x_2949_);
v___x_2951_ = ((size_t)0ULL);
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_2950_, v___x_2951_, v___x_2949_);
v_msg_2953_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2953_, 0, v_data_2920_);
lean_ctor_set(v_msg_2953_, 1, v_msg_2922_);
lean_ctor_set(v_msg_2953_, 2, v___x_2952_);
v___x_2954_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2953_, v___y_2923_, v___y_2924_, v___x_2948_, v___y_2926_);
lean_dec_ref_known(v___x_2948_, 14);
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_2992_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2992_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; lean_object* v_traceState_2960_; lean_object* v_env_2961_; lean_object* v_nextMacroScope_2962_; lean_object* v_ngen_2963_; lean_object* v_auxDeclNGen_2964_; lean_object* v_cache_2965_; lean_object* v_messages_2966_; lean_object* v_infoState_2967_; lean_object* v_snapshotTasks_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2991_; 
v___x_2959_ = lean_st_ref_take(v___y_2926_);
v_traceState_2960_ = lean_ctor_get(v___x_2959_, 4);
v_env_2961_ = lean_ctor_get(v___x_2959_, 0);
v_nextMacroScope_2962_ = lean_ctor_get(v___x_2959_, 1);
v_ngen_2963_ = lean_ctor_get(v___x_2959_, 2);
v_auxDeclNGen_2964_ = lean_ctor_get(v___x_2959_, 3);
v_cache_2965_ = lean_ctor_get(v___x_2959_, 5);
v_messages_2966_ = lean_ctor_get(v___x_2959_, 6);
v_infoState_2967_ = lean_ctor_get(v___x_2959_, 7);
v_snapshotTasks_2968_ = lean_ctor_get(v___x_2959_, 8);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2970_ = v___x_2959_;
v_isShared_2971_ = v_isSharedCheck_2991_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_snapshotTasks_2968_);
lean_inc(v_infoState_2967_);
lean_inc(v_messages_2966_);
lean_inc(v_cache_2965_);
lean_inc(v_traceState_2960_);
lean_inc(v_auxDeclNGen_2964_);
lean_inc(v_ngen_2963_);
lean_inc(v_nextMacroScope_2962_);
lean_inc(v_env_2961_);
lean_dec(v___x_2959_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2991_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
uint64_t v_tid_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2989_; 
v_tid_2972_ = lean_ctor_get_uint64(v_traceState_2960_, sizeof(void*)*1);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_traceState_2960_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; 
v_unused_2990_ = lean_ctor_get(v_traceState_2960_, 0);
lean_dec(v_unused_2990_);
v___x_2974_ = v_traceState_2960_;
v_isShared_2975_ = v_isSharedCheck_2989_;
goto v_resetjp_2973_;
}
else
{
lean_dec(v_traceState_2960_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2989_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2979_; 
v___x_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2976_, 0, v_ref_2921_);
lean_ctor_set(v___x_2976_, 1, v_a_2955_);
v___x_2977_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2919_, v___x_2976_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2977_);
v___x_2979_ = v___x_2974_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2977_);
lean_ctor_set_uint64(v_reuseFailAlloc_2988_, sizeof(void*)*1, v_tid_2972_);
v___x_2979_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2981_; 
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 4, v___x_2979_);
v___x_2981_ = v___x_2970_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_env_2961_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_nextMacroScope_2962_);
lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_ngen_2963_);
lean_ctor_set(v_reuseFailAlloc_2987_, 3, v_auxDeclNGen_2964_);
lean_ctor_set(v_reuseFailAlloc_2987_, 4, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2987_, 5, v_cache_2965_);
lean_ctor_set(v_reuseFailAlloc_2987_, 6, v_messages_2966_);
lean_ctor_set(v_reuseFailAlloc_2987_, 7, v_infoState_2967_);
lean_ctor_set(v_reuseFailAlloc_2987_, 8, v_snapshotTasks_2968_);
v___x_2981_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2982_ = lean_st_ref_set(v___y_2926_, v___x_2981_);
v___x_2983_ = lean_box(0);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 0, v___x_2983_);
v___x_2985_ = v___x_2957_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2983_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_2993_, lean_object* v_data_2994_, lean_object* v_ref_2995_, lean_object* v_msg_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2993_, v_data_2994_, v_ref_2995_, v_msg_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
return v_res_3002_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_3005_ = l_Lean_stringToMessageData(v___x_3004_);
return v___x_3005_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3006_; double v___x_3007_; 
v___x_3006_ = lean_unsigned_to_nat(1000u);
v___x_3007_ = lean_float_of_nat(v___x_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_3008_, uint8_t v_collapsed_3009_, lean_object* v_tag_3010_, lean_object* v_opts_3011_, uint8_t v_clsEnabled_3012_, lean_object* v_oldTraces_3013_, lean_object* v_msg_3014_, lean_object* v_resStartStop_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_fst_3026_; lean_object* v_snd_3027_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v_data_3031_; lean_object* v_fst_3042_; lean_object* v_snd_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; lean_object* v___y_3047_; lean_object* v_a_3048_; uint8_t v___y_3063_; double v___y_3094_; 
v_fst_3026_ = lean_ctor_get(v_resStartStop_3015_, 0);
lean_inc(v_fst_3026_);
v_snd_3027_ = lean_ctor_get(v_resStartStop_3015_, 1);
lean_inc(v_snd_3027_);
lean_dec_ref(v_resStartStop_3015_);
v_fst_3042_ = lean_ctor_get(v_snd_3027_, 0);
lean_inc(v_fst_3042_);
v_snd_3043_ = lean_ctor_get(v_snd_3027_, 1);
lean_inc(v_snd_3043_);
lean_dec(v_snd_3027_);
v___x_3044_ = l_Lean_trace_profiler;
v___x_3045_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_3011_, v___x_3044_);
if (v___x_3045_ == 0)
{
v___y_3063_ = v___x_3045_;
goto v___jp_3062_;
}
else
{
lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3099_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3100_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_3011_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; double v___x_3103_; double v___x_3104_; double v___x_3105_; 
v___x_3101_ = l_Lean_trace_profiler_threshold;
v___x_3102_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_3011_, v___x_3101_);
v___x_3103_ = lean_float_of_nat(v___x_3102_);
v___x_3104_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_3105_ = lean_float_div(v___x_3103_, v___x_3104_);
v___y_3094_ = v___x_3105_;
goto v___jp_3093_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; double v___x_3108_; 
v___x_3106_ = l_Lean_trace_profiler_threshold;
v___x_3107_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_3011_, v___x_3106_);
v___x_3108_ = lean_float_of_nat(v___x_3107_);
v___y_3094_ = v___x_3108_;
goto v___jp_3093_;
}
}
v___jp_3028_:
{
lean_object* v___x_3032_; 
lean_inc(v___y_3030_);
v___x_3032_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3013_, v_data_3031_, v___y_3030_, v___y_3029_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v___x_3033_; 
lean_dec_ref_known(v___x_3032_, 1);
v___x_3033_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_3026_);
return v___x_3033_;
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_fst_3026_);
v_a_3034_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3032_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3032_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
v___jp_3046_:
{
uint8_t v_result_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; double v___x_3052_; lean_object* v_data_3053_; 
v_result_3049_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_fst_3026_);
v___x_3050_ = lean_box(v_result_3049_);
v___x_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
v___x_3052_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_3010_);
lean_inc_ref(v___x_3051_);
lean_inc(v_cls_3008_);
v_data_3053_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3053_, 0, v_cls_3008_);
lean_ctor_set(v_data_3053_, 1, v___x_3051_);
lean_ctor_set(v_data_3053_, 2, v_tag_3010_);
lean_ctor_set_float(v_data_3053_, sizeof(void*)*3, v___x_3052_);
lean_ctor_set_float(v_data_3053_, sizeof(void*)*3 + 8, v___x_3052_);
lean_ctor_set_uint8(v_data_3053_, sizeof(void*)*3 + 16, v_collapsed_3009_);
if (v___x_3045_ == 0)
{
lean_dec_ref_known(v___x_3051_, 1);
lean_dec(v_snd_3043_);
lean_dec(v_fst_3042_);
lean_dec_ref(v_tag_3010_);
lean_dec(v_cls_3008_);
v___y_3029_ = v_a_3048_;
v___y_3030_ = v___y_3047_;
v_data_3031_ = v_data_3053_;
goto v___jp_3028_;
}
else
{
lean_object* v_data_3054_; double v___x_3055_; double v___x_3056_; 
lean_dec_ref_known(v_data_3053_, 3);
v_data_3054_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3054_, 0, v_cls_3008_);
lean_ctor_set(v_data_3054_, 1, v___x_3051_);
lean_ctor_set(v_data_3054_, 2, v_tag_3010_);
v___x_3055_ = lean_unbox_float(v_fst_3042_);
lean_dec(v_fst_3042_);
lean_ctor_set_float(v_data_3054_, sizeof(void*)*3, v___x_3055_);
v___x_3056_ = lean_unbox_float(v_snd_3043_);
lean_dec(v_snd_3043_);
lean_ctor_set_float(v_data_3054_, sizeof(void*)*3 + 8, v___x_3056_);
lean_ctor_set_uint8(v_data_3054_, sizeof(void*)*3 + 16, v_collapsed_3009_);
v___y_3029_ = v_a_3048_;
v___y_3030_ = v___y_3047_;
v_data_3031_ = v_data_3054_;
goto v___jp_3028_;
}
}
v___jp_3057_:
{
lean_object* v_ref_3058_; lean_object* v___x_3059_; 
v_ref_3058_ = lean_ctor_get(v___y_3023_, 5);
lean_inc(v___y_3024_);
lean_inc_ref(v___y_3023_);
lean_inc(v___y_3022_);
lean_inc_ref(v___y_3021_);
lean_inc(v___y_3020_);
lean_inc_ref(v___y_3019_);
lean_inc(v___y_3018_);
lean_inc_ref(v___y_3017_);
lean_inc(v___y_3016_);
lean_inc(v_fst_3026_);
v___x_3059_ = lean_apply_11(v_msg_3014_, v_fst_3026_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, lean_box(0));
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v___y_3047_ = v_ref_3058_;
v_a_3048_ = v_a_3060_;
goto v___jp_3046_;
}
else
{
lean_object* v___x_3061_; 
lean_dec_ref_known(v___x_3059_, 1);
v___x_3061_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_3047_ = v_ref_3058_;
v_a_3048_ = v___x_3061_;
goto v___jp_3046_;
}
}
v___jp_3062_:
{
if (v_clsEnabled_3012_ == 0)
{
if (v___y_3063_ == 0)
{
lean_object* v___x_3064_; lean_object* v_traceState_3065_; lean_object* v_env_3066_; lean_object* v_nextMacroScope_3067_; lean_object* v_ngen_3068_; lean_object* v_auxDeclNGen_3069_; lean_object* v_cache_3070_; lean_object* v_messages_3071_; lean_object* v_infoState_3072_; lean_object* v_snapshotTasks_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v_snd_3043_);
lean_dec(v_fst_3042_);
lean_dec_ref(v_msg_3014_);
lean_dec_ref(v_tag_3010_);
lean_dec(v_cls_3008_);
v___x_3064_ = lean_st_ref_take(v___y_3024_);
v_traceState_3065_ = lean_ctor_get(v___x_3064_, 4);
v_env_3066_ = lean_ctor_get(v___x_3064_, 0);
v_nextMacroScope_3067_ = lean_ctor_get(v___x_3064_, 1);
v_ngen_3068_ = lean_ctor_get(v___x_3064_, 2);
v_auxDeclNGen_3069_ = lean_ctor_get(v___x_3064_, 3);
v_cache_3070_ = lean_ctor_get(v___x_3064_, 5);
v_messages_3071_ = lean_ctor_get(v___x_3064_, 6);
v_infoState_3072_ = lean_ctor_get(v___x_3064_, 7);
v_snapshotTasks_3073_ = lean_ctor_get(v___x_3064_, 8);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3075_ = v___x_3064_;
v_isShared_3076_ = v_isSharedCheck_3092_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_snapshotTasks_3073_);
lean_inc(v_infoState_3072_);
lean_inc(v_messages_3071_);
lean_inc(v_cache_3070_);
lean_inc(v_traceState_3065_);
lean_inc(v_auxDeclNGen_3069_);
lean_inc(v_ngen_3068_);
lean_inc(v_nextMacroScope_3067_);
lean_inc(v_env_3066_);
lean_dec(v___x_3064_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3092_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
uint64_t v_tid_3077_; lean_object* v_traces_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3091_; 
v_tid_3077_ = lean_ctor_get_uint64(v_traceState_3065_, sizeof(void*)*1);
v_traces_3078_ = lean_ctor_get(v_traceState_3065_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_traceState_3065_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3080_ = v_traceState_3065_;
v_isShared_3081_ = v_isSharedCheck_3091_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_traces_3078_);
lean_dec(v_traceState_3065_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3091_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
v___x_3082_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3013_, v_traces_3078_);
lean_dec_ref(v_traces_3078_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3082_);
v___x_3084_ = v___x_3080_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3082_);
lean_ctor_set_uint64(v_reuseFailAlloc_3090_, sizeof(void*)*1, v_tid_3077_);
v___x_3084_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3086_; 
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 4, v___x_3084_);
v___x_3086_ = v___x_3075_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_env_3066_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_nextMacroScope_3067_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_ngen_3068_);
lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_auxDeclNGen_3069_);
lean_ctor_set(v_reuseFailAlloc_3089_, 4, v___x_3084_);
lean_ctor_set(v_reuseFailAlloc_3089_, 5, v_cache_3070_);
lean_ctor_set(v_reuseFailAlloc_3089_, 6, v_messages_3071_);
lean_ctor_set(v_reuseFailAlloc_3089_, 7, v_infoState_3072_);
lean_ctor_set(v_reuseFailAlloc_3089_, 8, v_snapshotTasks_3073_);
v___x_3086_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = lean_st_ref_set(v___y_3024_, v___x_3086_);
v___x_3088_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_3026_);
return v___x_3088_;
}
}
}
}
}
else
{
goto v___jp_3057_;
}
}
else
{
goto v___jp_3057_;
}
}
v___jp_3093_:
{
double v___x_3095_; double v___x_3096_; double v___x_3097_; uint8_t v___x_3098_; 
v___x_3095_ = lean_unbox_float(v_snd_3043_);
v___x_3096_ = lean_unbox_float(v_fst_3042_);
v___x_3097_ = lean_float_sub(v___x_3095_, v___x_3096_);
v___x_3098_ = lean_float_decLt(v___y_3094_, v___x_3097_);
v___y_3063_ = v___x_3098_;
goto v___jp_3062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object** _args){
lean_object* v_cls_3109_ = _args[0];
lean_object* v_collapsed_3110_ = _args[1];
lean_object* v_tag_3111_ = _args[2];
lean_object* v_opts_3112_ = _args[3];
lean_object* v_clsEnabled_3113_ = _args[4];
lean_object* v_oldTraces_3114_ = _args[5];
lean_object* v_msg_3115_ = _args[6];
lean_object* v_resStartStop_3116_ = _args[7];
lean_object* v___y_3117_ = _args[8];
lean_object* v___y_3118_ = _args[9];
lean_object* v___y_3119_ = _args[10];
lean_object* v___y_3120_ = _args[11];
lean_object* v___y_3121_ = _args[12];
lean_object* v___y_3122_ = _args[13];
lean_object* v___y_3123_ = _args[14];
lean_object* v___y_3124_ = _args[15];
lean_object* v___y_3125_ = _args[16];
lean_object* v___y_3126_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3127_; uint8_t v_clsEnabled_boxed_3128_; lean_object* v_res_3129_; 
v_collapsed_boxed_3127_ = lean_unbox(v_collapsed_3110_);
v_clsEnabled_boxed_3128_ = lean_unbox(v_clsEnabled_3113_);
v_res_3129_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3109_, v_collapsed_boxed_3127_, v_tag_3111_, v_opts_3112_, v_clsEnabled_boxed_3128_, v_oldTraces_3114_, v_msg_3115_, v_resStartStop_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v_opts_3112_);
return v_res_3129_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2));
v___x_3136_ = l_Lean_stringToMessageData(v___x_3135_);
return v___x_3136_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5(void){
_start:
{
lean_object* v___x_3138_; double v___x_3139_; 
v___x_3138_ = lean_unsigned_to_nat(1000000000u);
v___x_3139_ = lean_float_of_nat(v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object* v_P_3140_, lean_object* v_lhs_3141_, lean_object* v_rhs_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_){
_start:
{
uint8_t v___y_3154_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v_options_3176_; lean_object* v_inheritedTraceOptions_3177_; uint8_t v_hasTrace_3178_; lean_object* v_cls_3179_; lean_object* v___f_3180_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; uint8_t v_____do__lift_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; 
v_options_3176_ = lean_ctor_get(v_a_3150_, 2);
v_inheritedTraceOptions_3177_ = lean_ctor_get(v_a_3150_, 13);
v_hasTrace_3178_ = lean_ctor_get_uint8(v_options_3176_, sizeof(void*)*1);
v_cls_3179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_3180_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1));
if (v_hasTrace_3178_ == 0)
{
lean_object* v___x_3304_; lean_object* v_a_3305_; uint8_t v___x_3306_; 
v___x_3304_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3179_, v_inheritedTraceOptions_3177_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref(v___x_3304_);
v___x_3306_ = lean_unbox(v_a_3305_);
lean_dec(v_a_3305_);
v_____do__lift_3281_ = v___x_3306_;
v___y_3282_ = v_a_3143_;
v___y_3283_ = v_a_3144_;
v___y_3284_ = v_a_3145_;
v___y_3285_ = v_a_3146_;
v___y_3286_ = v_a_3147_;
v___y_3287_ = v_a_3148_;
v___y_3288_ = v_a_3149_;
v___y_3289_ = v_a_3150_;
v___y_3290_ = v_a_3151_;
goto v___jp_3280_;
}
else
{
lean_object* v___f_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v_a_3315_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v_a_3327_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v_a_3345_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v_a_3360_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; 
v___f_3307_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4));
v___x_3308_ = 0;
v___x_3309_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3311_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3177_, v_options_3176_, v___x_3310_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3408_ = l_Lean_trace_profiler;
v___x_3409_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_3176_, v___x_3408_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; lean_object* v_a_3411_; uint8_t v___x_3412_; 
v___x_3410_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3179_, v_inheritedTraceOptions_3177_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref(v___x_3410_);
v___x_3412_ = lean_unbox(v_a_3411_);
lean_dec(v_a_3411_);
v_____do__lift_3281_ = v___x_3412_;
v___y_3282_ = v_a_3143_;
v___y_3283_ = v_a_3144_;
v___y_3284_ = v_a_3145_;
v___y_3285_ = v_a_3146_;
v___y_3286_ = v_a_3147_;
v___y_3287_ = v_a_3148_;
v___y_3288_ = v_a_3149_;
v___y_3289_ = v_a_3150_;
v___y_3290_ = v_a_3151_;
goto v___jp_3280_;
}
else
{
goto v___jp_3375_;
}
}
else
{
goto v___jp_3375_;
}
v___jp_3312_:
{
lean_object* v___x_3316_; double v___x_3317_; double v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3316_ = lean_io_get_num_heartbeats();
v___x_3317_ = lean_float_of_nat(v___y_3313_);
v___x_3318_ = lean_float_of_nat(v___x_3316_);
v___x_3319_ = lean_box_float(v___x_3317_);
v___x_3320_ = lean_box_float(v___x_3318_);
v___x_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3319_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___x_3322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3322_, 0, v_a_3315_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3179_, v___x_3308_, v___x_3309_, v_options_3176_, v___x_3311_, v___y_3314_, v___f_3307_, v___x_3322_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
return v___x_3323_;
}
v___jp_3324_:
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_a_3327_);
v___y_3313_ = v___y_3325_;
v___y_3314_ = v___y_3326_;
v_a_3315_ = v___x_3328_;
goto v___jp_3312_;
}
v___jp_3329_:
{
if (lean_obj_tag(v___y_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
v_a_3333_ = lean_ctor_get(v___y_3332_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___y_3332_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___y_3332_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___y_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set_tag(v___x_3335_, 1);
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
v___y_3313_ = v___y_3330_;
v___y_3314_ = v___y_3331_;
v_a_3315_ = v___x_3338_;
goto v___jp_3312_;
}
}
}
else
{
lean_object* v_a_3341_; 
v_a_3341_ = lean_ctor_get(v___y_3332_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___y_3332_, 1);
v___y_3325_ = v___y_3330_;
v___y_3326_ = v___y_3331_;
v_a_3327_ = v_a_3341_;
goto v___jp_3324_;
}
}
v___jp_3342_:
{
lean_object* v___x_3346_; double v___x_3347_; double v___x_3348_; double v___x_3349_; double v___x_3350_; double v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3346_ = lean_io_mono_nanos_now();
v___x_3347_ = lean_float_of_nat(v___y_3344_);
v___x_3348_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5);
v___x_3349_ = lean_float_div(v___x_3347_, v___x_3348_);
v___x_3350_ = lean_float_of_nat(v___x_3346_);
v___x_3351_ = lean_float_div(v___x_3350_, v___x_3348_);
v___x_3352_ = lean_box_float(v___x_3349_);
v___x_3353_ = lean_box_float(v___x_3351_);
v___x_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3352_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v_a_3345_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3179_, v___x_3308_, v___x_3309_, v_options_3176_, v___x_3311_, v___y_3343_, v___f_3307_, v___x_3355_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
return v___x_3356_;
}
v___jp_3357_:
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3361_, 0, v_a_3360_);
v___y_3343_ = v___y_3358_;
v___y_3344_ = v___y_3359_;
v_a_3345_ = v___x_3361_;
goto v___jp_3342_;
}
v___jp_3362_:
{
if (lean_obj_tag(v___y_3365_) == 0)
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
v_a_3366_ = lean_ctor_get(v___y_3365_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___y_3365_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___y_3365_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___y_3365_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set_tag(v___x_3368_, 1);
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
v___y_3343_ = v___y_3363_;
v___y_3344_ = v___y_3364_;
v_a_3345_ = v___x_3371_;
goto v___jp_3342_;
}
}
}
else
{
lean_object* v_a_3374_; 
v_a_3374_ = lean_ctor_get(v___y_3365_, 0);
lean_inc(v_a_3374_);
lean_dec_ref_known(v___y_3365_, 1);
v___y_3358_ = v___y_3363_;
v___y_3359_ = v___y_3364_;
v_a_3360_ = v_a_3374_;
goto v___jp_3357_;
}
}
v___jp_3375_:
{
lean_object* v___x_3376_; lean_object* v_a_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3376_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_3151_);
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref(v___x_3376_);
v___x_3378_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3379_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_3176_, v___x_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v_a_3382_; uint8_t v___x_3383_; 
v___x_3380_ = lean_io_mono_nanos_now();
v___x_3381_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3179_, v_inheritedTraceOptions_3177_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref(v___x_3381_);
v___x_3383_ = lean_unbox(v_a_3382_);
lean_dec(v_a_3382_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = lean_box(0);
v___x_3385_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_3141_, v_rhs_3142_, v___x_3379_, v___f_3180_, v_cls_3179_, v_P_3140_, v___x_3384_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
v___y_3363_ = v_a_3377_;
v___y_3364_ = v___x_3380_;
v___y_3365_ = v___x_3385_;
goto v___jp_3362_;
}
else
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3386_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_3142_);
lean_inc_ref(v_lhs_3141_);
lean_inc_ref(v_P_3140_);
v___x_3387_ = l_Lean_mkAppB(v_P_3140_, v_lhs_3141_, v_rhs_3142_);
v___x_3388_ = l_Lean_indentExpr(v___x_3387_);
v___x_3389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3386_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3179_, v___x_3389_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___x_3392_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3390_, 1);
v___x_3392_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_3141_, v_rhs_3142_, v___x_3379_, v___f_3180_, v_cls_3179_, v_P_3140_, v_a_3391_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
v___y_3363_ = v_a_3377_;
v___y_3364_ = v___x_3380_;
v___y_3365_ = v___x_3392_;
goto v___jp_3362_;
}
else
{
lean_object* v_a_3393_; 
lean_dec_ref(v_rhs_3142_);
lean_dec_ref(v_lhs_3141_);
lean_dec_ref(v_P_3140_);
v_a_3393_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3390_, 1);
v___y_3358_ = v_a_3377_;
v___y_3359_ = v___x_3380_;
v_a_3360_ = v_a_3393_;
goto v___jp_3357_;
}
}
}
else
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v_a_3396_; uint8_t v___x_3397_; 
v___x_3394_ = lean_io_get_num_heartbeats();
v___x_3395_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3179_, v_inheritedTraceOptions_3177_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref(v___x_3395_);
v___x_3397_ = lean_unbox(v_a_3396_);
lean_dec(v_a_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = lean_box(0);
v___x_3399_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_3141_, v_rhs_3142_, v_P_3140_, v_cls_3179_, v___x_3379_, v___f_3180_, v___x_3308_, v___x_3398_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
v___y_3330_ = v___x_3394_;
v___y_3331_ = v_a_3377_;
v___y_3332_ = v___x_3399_;
goto v___jp_3329_;
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3400_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_3142_);
lean_inc_ref(v_lhs_3141_);
lean_inc_ref(v_P_3140_);
v___x_3401_ = l_Lean_mkAppB(v_P_3140_, v_lhs_3141_, v_rhs_3142_);
v___x_3402_ = l_Lean_indentExpr(v___x_3401_);
v___x_3403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3400_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
v___x_3404_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3179_, v___x_3403_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3406_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref_known(v___x_3404_, 1);
v___x_3406_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_3141_, v_rhs_3142_, v_P_3140_, v_cls_3179_, v___x_3379_, v___f_3180_, v___x_3308_, v_a_3405_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
v___y_3330_ = v___x_3394_;
v___y_3331_ = v_a_3377_;
v___y_3332_ = v___x_3406_;
goto v___jp_3329_;
}
else
{
lean_object* v_a_3407_; 
lean_dec_ref(v_rhs_3142_);
lean_dec_ref(v_lhs_3141_);
lean_dec_ref(v_P_3140_);
v_a_3407_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3404_, 1);
v___y_3325_ = v___x_3394_;
v___y_3326_ = v_a_3377_;
v_a_3327_ = v_a_3407_;
goto v___jp_3324_;
}
}
}
}
}
v___jp_3153_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3155_, 0, v___y_3154_);
lean_ctor_set_uint8(v___x_3155_, 1, v___y_3154_);
v___x_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
return v___x_3156_;
}
v___jp_3157_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
return v___x_3159_;
}
v___jp_3160_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
return v___x_3162_;
}
v___jp_3163_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3172_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__7);
v___x_3173_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__8));
v___x_3174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3174_, 0, v___y_3165_);
lean_ctor_set(v___x_3174_, 1, v___x_3172_);
lean_ctor_set(v___x_3174_, 2, v___x_3173_);
v___x_3175_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_3164_, v___x_3174_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
return v___x_3175_;
}
v___jp_3181_:
{
lean_object* v___x_3191_; 
lean_inc_ref(v_lhs_3141_);
v___x_3191_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_3141_);
if (lean_obj_tag(v___x_3191_) == 1)
{
lean_object* v_val_3192_; lean_object* v___x_3193_; 
v_val_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_val_3192_);
lean_dec_ref_known(v___x_3191_, 1);
lean_inc_ref(v_rhs_3142_);
v___x_3193_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_3142_);
if (lean_obj_tag(v___x_3193_) == 1)
{
lean_object* v_val_3194_; uint8_t v___x_3195_; 
v_val_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_val_3194_);
lean_dec_ref_known(v___x_3193_, 1);
v___x_3195_ = lean_expr_eqv(v_val_3192_, v_val_3194_);
if (v___x_3195_ == 0)
{
lean_object* v_inheritedTraceOptions_3196_; lean_object* v___x_3197_; lean_object* v_a_3198_; uint8_t v___x_3199_; 
lean_dec_ref(v_P_3140_);
v_inheritedTraceOptions_3196_ = lean_ctor_get(v___y_3189_, 13);
v___x_3197_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3179_, v_inheritedTraceOptions_3196_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref(v___x_3197_);
v___x_3199_ = lean_unbox(v_a_3198_);
lean_dec(v_a_3198_);
if (v___x_3199_ == 0)
{
lean_dec(v_val_3194_);
lean_dec(v_val_3192_);
lean_dec_ref(v_rhs_3142_);
lean_dec_ref(v_lhs_3141_);
v___y_3154_ = v___x_3195_;
goto v___jp_3153_;
}
else
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3200_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__1);
v___x_3201_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3192_);
v___x_3202_ = l_Lean_MessageData_ofExpr(v___x_3201_);
v___x_3203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3200_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
v___x_3204_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__3);
v___x_3205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3203_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = l_Lean_indentExpr(v_lhs_3141_);
v___x_3207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3205_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v___x_3208_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__5);
v___x_3209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3207_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3194_);
v___x_3211_ = l_Lean_MessageData_ofExpr(v___x_3210_);
v___x_3212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3209_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
lean_ctor_set(v___x_3213_, 1, v___x_3204_);
v___x_3214_ = l_Lean_indentExpr(v_rhs_3142_);
v___x_3215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3213_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3179_, v___x_3215_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_dec_ref_known(v___x_3216_, 1);
v___y_3154_ = v___x_3195_;
goto v___jp_3153_;
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
v_a_3217_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3216_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3216_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
}
else
{
lean_object* v_options_3225_; lean_object* v_inheritedTraceOptions_3226_; uint8_t v_hasTrace_3227_; uint8_t v___x_3228_; lean_object* v___x_3229_; lean_object* v___f_3230_; 
lean_dec(v_val_3194_);
v_options_3225_ = lean_ctor_get(v___y_3189_, 2);
v_inheritedTraceOptions_3226_ = lean_ctor_get(v___y_3189_, 13);
v_hasTrace_3227_ = lean_ctor_get_uint8(v_options_3225_, sizeof(void*)*1);
v___x_3228_ = 0;
v___x_3229_ = lean_box(v___x_3228_);
lean_inc(v_val_3192_);
v___f_3230_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_3230_, 0, v_val_3192_);
lean_closure_set(v___f_3230_, 1, v_lhs_3141_);
lean_closure_set(v___f_3230_, 2, v_rhs_3142_);
lean_closure_set(v___f_3230_, 3, v_P_3140_);
lean_closure_set(v___f_3230_, 4, v___x_3229_);
if (v_hasTrace_3227_ == 0)
{
v___y_3164_ = v___f_3230_;
v___y_3165_ = v_val_3192_;
v___y_3166_ = v___y_3185_;
v___y_3167_ = v___y_3186_;
v___y_3168_ = v___y_3187_;
v___y_3169_ = v___y_3188_;
v___y_3170_ = v___y_3189_;
v___y_3171_ = v___y_3190_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3232_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3226_, v_options_3225_, v___x_3231_);
if (v___x_3232_ == 0)
{
v___y_3164_ = v___f_3230_;
v___y_3165_ = v_val_3192_;
v___y_3166_ = v___y_3185_;
v___y_3167_ = v___y_3186_;
v___y_3168_ = v___y_3187_;
v___y_3169_ = v___y_3188_;
v___y_3170_ = v___y_3189_;
v___y_3171_ = v___y_3190_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3233_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__10);
lean_inc(v_val_3192_);
v___x_3234_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3192_);
v___x_3235_ = l_Lean_MessageData_ofExpr(v___x_3234_);
v___x_3236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3233_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__12);
v___x_3238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___x_3239_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3179_, v___x_3238_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_dec_ref_known(v___x_3239_, 1);
v___y_3164_ = v___f_3230_;
v___y_3165_ = v_val_3192_;
v___y_3166_ = v___y_3185_;
v___y_3167_ = v___y_3186_;
v___y_3168_ = v___y_3187_;
v___y_3169_ = v___y_3188_;
v___y_3170_ = v___y_3189_;
v___y_3171_ = v___y_3190_;
goto v___jp_3163_;
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref(v___f_3230_);
lean_dec(v_val_3192_);
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3248_; lean_object* v___x_3249_; lean_object* v_a_3250_; uint8_t v___x_3251_; 
lean_dec(v___x_3193_);
lean_dec(v_val_3192_);
lean_dec_ref(v_lhs_3141_);
lean_dec_ref(v_P_3140_);
v_inheritedTraceOptions_3248_ = lean_ctor_get(v___y_3189_, 13);
v___x_3249_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3179_, v_inheritedTraceOptions_3248_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref(v___x_3249_);
v___x_3251_ = lean_unbox(v_a_3250_);
lean_dec(v_a_3250_);
if (v___x_3251_ == 0)
{
lean_dec_ref(v_rhs_3142_);
goto v___jp_3160_;
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3252_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14);
v___x_3253_ = l_Lean_indentExpr(v_rhs_3142_);
v___x_3254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3179_, v___x_3254_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_dec_ref_known(v___x_3255_, 1);
goto v___jp_3160_;
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3255_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3255_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3264_; lean_object* v___x_3265_; lean_object* v_a_3266_; uint8_t v___x_3267_; 
lean_dec(v___x_3191_);
lean_dec_ref(v_rhs_3142_);
lean_dec_ref(v_P_3140_);
v_inheritedTraceOptions_3264_ = lean_ctor_get(v___y_3189_, 13);
v___x_3265_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3179_, v_inheritedTraceOptions_3264_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref(v___x_3265_);
v___x_3267_ = lean_unbox(v_a_3266_);
lean_dec(v_a_3266_);
if (v___x_3267_ == 0)
{
lean_dec_ref(v_lhs_3141_);
goto v___jp_3157_;
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3268_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___closed__14);
v___x_3269_ = l_Lean_indentExpr(v_lhs_3141_);
v___x_3270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3268_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3179_, v___x_3270_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_dec_ref_known(v___x_3271_, 1);
goto v___jp_3157_;
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
}
}
v___jp_3280_:
{
if (v_____do__lift_3281_ == 0)
{
v___y_3182_ = v___y_3282_;
v___y_3183_ = v___y_3283_;
v___y_3184_ = v___y_3284_;
v___y_3185_ = v___y_3285_;
v___y_3186_ = v___y_3286_;
v___y_3187_ = v___y_3287_;
v___y_3188_ = v___y_3288_;
v___y_3189_ = v___y_3289_;
v___y_3190_ = v___y_3290_;
goto v___jp_3181_;
}
else
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3291_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_3142_);
lean_inc_ref(v_lhs_3141_);
lean_inc_ref(v_P_3140_);
v___x_3292_ = l_Lean_mkAppB(v_P_3140_, v_lhs_3141_, v_rhs_3142_);
v___x_3293_ = l_Lean_indentExpr(v___x_3292_);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3291_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3179_, v___x_3294_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_dec_ref_known(v___x_3295_, 1);
v___y_3182_ = v___y_3282_;
v___y_3183_ = v___y_3283_;
v___y_3184_ = v___y_3284_;
v___y_3185_ = v___y_3285_;
v___y_3186_ = v___y_3286_;
v___y_3187_ = v___y_3287_;
v___y_3188_ = v___y_3288_;
v___y_3189_ = v___y_3289_;
v___y_3190_ = v___y_3290_;
goto v___jp_3181_;
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec_ref(v_rhs_3142_);
lean_dec_ref(v_lhs_3141_);
lean_dec_ref(v_P_3140_);
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3295_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3295_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3413_, lean_object* v_lhs_3414_, lean_object* v_rhs_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v_P_3413_, v_lhs_3414_, v_rhs_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3423_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3421_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec(v_a_3416_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3427_, lean_object* v_msg_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3427_, v_msg_3428_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3440_, lean_object* v_msg_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(v_cls_3440_, v_msg_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_00_u03b1_3453_, lean_object* v_x_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v___x_3465_; 
v___x_3465_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_3454_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3466_, lean_object* v_x_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_00_u03b1_3466_, v_x_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_oldTraces_3479_, lean_object* v_data_3480_, lean_object* v_ref_3481_, lean_object* v_msg_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3479_, v_data_3480_, v_ref_3481_, v_msg_3482_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_oldTraces_3494_, lean_object* v_data_3495_, lean_object* v_ref_3496_, lean_object* v_msg_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_oldTraces_3494_, v_data_3495_, v_ref_3496_, v_msg_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(lean_object* v_x_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0___boxed(lean_object* v_x_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v_x_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(lean_object* v_arg_3539_, lean_object* v_arg_3540_, lean_object* v_arg_3541_, lean_object* v_arg_3542_, lean_object* v_____r_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v___x_3554_; 
lean_inc_ref(v_arg_3539_);
v___x_3554_ = l_Lean_Meta_getDecLevel(v_arg_3539_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3554_, 1);
v___x_3556_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3557_ = lean_box(0);
v___x_3558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3558_, 0, v_a_3555_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
v___x_3559_ = l_Lean_Expr_const___override(v___x_3556_, v___x_3558_);
v___x_3560_ = l_Lean_mkAppB(v___x_3559_, v_arg_3539_, v_arg_3540_);
v___x_3561_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3560_, v_arg_3541_, v_arg_3542_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
return v___x_3561_;
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec_ref(v_arg_3542_);
lean_dec_ref(v_arg_3541_);
lean_dec_ref(v_arg_3540_);
lean_dec_ref(v_arg_3539_);
v_a_3562_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3554_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3554_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___boxed(lean_object* v_arg_3570_, lean_object* v_arg_3571_, lean_object* v_arg_3572_, lean_object* v_arg_3573_, lean_object* v_____r_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3570_, v_arg_3571_, v_arg_3572_, v_arg_3573_, v_____r_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(lean_object* v_arg_3589_, lean_object* v_arg_3590_, lean_object* v_arg_3591_, lean_object* v_____r_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; 
lean_inc_ref(v_arg_3589_);
v___x_3603_ = l_Lean_Meta_getLevel(v_arg_3589_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3603_, 1);
v___x_3605_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3606_ = lean_box(0);
v___x_3607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3607_, 0, v_a_3604_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = l_Lean_Expr_const___override(v___x_3605_, v___x_3607_);
v___x_3609_ = l_Lean_Expr_app___override(v___x_3608_, v_arg_3589_);
v___x_3610_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3609_, v_arg_3590_, v_arg_3591_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
return v___x_3610_;
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref(v_arg_3591_);
lean_dec_ref(v_arg_3590_);
lean_dec_ref(v_arg_3589_);
v_a_3611_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3603_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3603_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___boxed(lean_object* v_arg_3619_, lean_object* v_arg_3620_, lean_object* v_arg_3621_, lean_object* v_____r_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3619_, v_arg_3620_, v_arg_3621_, v_____r_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3623_);
return v_res_3633_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1(void){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0));
v___x_3636_ = l_Lean_stringToMessageData(v___x_3635_);
return v___x_3636_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = l_Lean_checkEmoji;
v___x_3638_ = l_Lean_stringToMessageData(v___x_3637_);
return v___x_3638_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3639_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2);
v___x_3640_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1);
v___x_3641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
lean_ctor_set(v___x_3641_, 1, v___x_3639_);
return v___x_3641_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5(void){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4));
v___x_3644_ = l_Lean_stringToMessageData(v___x_3643_);
return v___x_3644_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3645_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5);
v___x_3646_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
lean_ctor_set(v___x_3647_, 1, v___x_3645_);
return v___x_3647_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7));
v___x_3650_ = l_Lean_stringToMessageData(v___x_3649_);
return v___x_3650_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3652_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
lean_ctor_set(v___x_3653_, 1, v___x_3651_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object* v_e_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v___y_3666_; lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3654_, v_a_3661_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3700_; uint8_t v___x_3701_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_a_3699_);
lean_dec_ref_known(v___x_3698_, 1);
v___x_3700_ = l_Lean_Expr_cleanupAnnotations(v_a_3699_);
v___x_3701_ = l_Lean_Expr_isApp(v___x_3700_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
lean_dec_ref(v___x_3700_);
v___x_3702_ = lean_box(0);
v___x_3703_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3702_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
v___y_3666_ = v___x_3703_;
goto v___jp_3665_;
}
else
{
lean_object* v_arg_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v_arg_3704_ = lean_ctor_get(v___x_3700_, 1);
lean_inc_ref(v_arg_3704_);
v___x_3705_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3700_);
v___x_3706_ = l_Lean_Expr_isApp(v___x_3705_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
lean_dec_ref(v___x_3705_);
lean_dec_ref(v_arg_3704_);
v___x_3707_ = lean_box(0);
v___x_3708_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3707_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
v___y_3666_ = v___x_3708_;
goto v___jp_3665_;
}
else
{
lean_object* v_arg_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; 
v_arg_3709_ = lean_ctor_get(v___x_3705_, 1);
lean_inc_ref(v_arg_3709_);
v___x_3710_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3705_);
v___x_3711_ = l_Lean_Expr_isApp(v___x_3710_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
lean_dec_ref(v___x_3710_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_arg_3704_);
v___x_3712_ = lean_box(0);
v___x_3713_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3712_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
v___y_3666_ = v___x_3713_;
goto v___jp_3665_;
}
else
{
lean_object* v_arg_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v_arg_3714_ = lean_ctor_get(v___x_3710_, 1);
lean_inc_ref(v_arg_3714_);
v___x_3715_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3710_);
v___x_3716_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3717_ = l_Lean_Expr_isConstOf(v___x_3715_, v___x_3716_);
if (v___x_3717_ == 0)
{
uint8_t v___x_3718_; 
v___x_3718_ = l_Lean_Expr_isApp(v___x_3715_);
if (v___x_3718_ == 0)
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
lean_dec_ref(v___x_3715_);
lean_dec_ref(v_arg_3714_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_arg_3704_);
v___x_3719_ = lean_box(0);
v___x_3720_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3719_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
v___y_3666_ = v___x_3720_;
goto v___jp_3665_;
}
else
{
lean_object* v_arg_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; uint8_t v___x_3724_; 
v_arg_3721_ = lean_ctor_get(v___x_3715_, 1);
lean_inc_ref(v_arg_3721_);
v___x_3722_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3715_);
v___x_3723_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3724_ = l_Lean_Expr_isConstOf(v___x_3722_, v___x_3723_);
lean_dec_ref(v___x_3722_);
if (v___x_3724_ == 0)
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
lean_dec_ref(v_arg_3721_);
lean_dec_ref(v_arg_3714_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_arg_3704_);
v___x_3725_ = lean_box(0);
v___x_3726_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3725_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
v___y_3666_ = v___x_3726_;
goto v___jp_3665_;
}
else
{
lean_object* v_options_3727_; lean_object* v_inheritedTraceOptions_3728_; uint8_t v_hasTrace_3729_; 
v_options_3727_ = lean_ctor_get(v_a_3662_, 2);
v_inheritedTraceOptions_3728_ = lean_ctor_get(v_a_3662_, 13);
v_hasTrace_3729_ = lean_ctor_get_uint8(v_options_3727_, sizeof(void*)*1);
if (v_hasTrace_3729_ == 0)
{
goto v___jp_3730_;
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; uint8_t v___x_3735_; 
v___x_3733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3735_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3728_, v_options_3727_, v___x_3734_);
if (v___x_3735_ == 0)
{
goto v___jp_3730_;
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6);
v___x_3737_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3733_, v___x_3736_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3739_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v___x_3737_, 1);
v___x_3739_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3721_, v_arg_3714_, v_arg_3709_, v_arg_3704_, v_a_3738_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
v___y_3666_ = v___x_3739_;
goto v___jp_3665_;
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_dec_ref(v_arg_3721_);
lean_dec_ref(v_arg_3714_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_arg_3704_);
v_a_3740_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3737_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3737_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
}
v___jp_3730_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = lean_box(0);
v___x_3732_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3721_, v_arg_3714_, v_arg_3709_, v_arg_3704_, v___x_3731_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
v___y_3666_ = v___x_3732_;
goto v___jp_3665_;
}
}
}
}
else
{
lean_object* v_options_3748_; lean_object* v_inheritedTraceOptions_3749_; uint8_t v_hasTrace_3750_; 
lean_dec_ref(v___x_3715_);
v_options_3748_ = lean_ctor_get(v_a_3662_, 2);
v_inheritedTraceOptions_3749_ = lean_ctor_get(v_a_3662_, 13);
v_hasTrace_3750_ = lean_ctor_get_uint8(v_options_3748_, sizeof(void*)*1);
if (v_hasTrace_3750_ == 0)
{
goto v___jp_3751_;
}
else
{
lean_object* v___x_3754_; lean_object* v___x_3755_; uint8_t v___x_3756_; 
v___x_3754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3756_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3749_, v_options_3748_, v___x_3755_);
if (v___x_3756_ == 0)
{
goto v___jp_3751_;
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3757_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9);
v___x_3758_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3754_, v___x_3757_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v___x_3760_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref_known(v___x_3758_, 1);
v___x_3760_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3714_, v_arg_3709_, v_arg_3704_, v_a_3759_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
v___y_3666_ = v___x_3760_;
goto v___jp_3665_;
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec_ref(v_arg_3714_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_arg_3704_);
v_a_3761_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3758_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3758_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
}
v___jp_3751_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_box(0);
v___x_3753_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3714_, v_arg_3709_, v_arg_3704_, v___x_3752_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
v___y_3666_ = v___x_3753_;
goto v___jp_3665_;
}
}
}
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
v_a_3769_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3698_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3698_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
v___jp_3665_:
{
if (lean_obj_tag(v___y_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3697_; 
v_a_3667_ = lean_ctor_get(v___y_3666_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___y_3666_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3669_ = v___y_3666_;
v_isShared_3670_ = v_isSharedCheck_3697_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___y_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3697_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
if (lean_obj_tag(v_a_3667_) == 0)
{
uint8_t v_contextDependent_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3682_; 
v_contextDependent_3671_ = lean_ctor_get_uint8(v_a_3667_, 1);
v_isSharedCheck_3682_ = !lean_is_exclusive(v_a_3667_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3673_ = v_a_3667_;
v_isShared_3674_ = v_isSharedCheck_3682_;
goto v_resetjp_3672_;
}
else
{
lean_dec(v_a_3667_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3682_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
uint8_t v___x_3675_; lean_object* v___x_3677_; 
v___x_3675_ = 1;
if (v_isShared_3674_ == 0)
{
v___x_3677_ = v___x_3673_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_3681_, 1, v_contextDependent_3671_);
v___x_3677_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3679_; 
lean_ctor_set_uint8(v___x_3677_, 0, v___x_3675_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3677_);
v___x_3679_ = v___x_3669_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_e_x27_3683_; lean_object* v_proof_3684_; uint8_t v_contextDependent_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3696_; 
v_e_x27_3683_ = lean_ctor_get(v_a_3667_, 0);
v_proof_3684_ = lean_ctor_get(v_a_3667_, 1);
v_contextDependent_3685_ = lean_ctor_get_uint8(v_a_3667_, sizeof(void*)*2 + 1);
v_isSharedCheck_3696_ = !lean_is_exclusive(v_a_3667_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3687_ = v_a_3667_;
v_isShared_3688_ = v_isSharedCheck_3696_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_proof_3684_);
lean_inc(v_e_x27_3683_);
lean_dec(v_a_3667_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3696_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
uint8_t v___x_3689_; lean_object* v___x_3691_; 
v___x_3689_ = 1;
if (v_isShared_3688_ == 0)
{
v___x_3691_ = v___x_3687_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_e_x27_3683_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v_proof_3684_);
lean_ctor_set_uint8(v_reuseFailAlloc_3695_, sizeof(void*)*2 + 1, v_contextDependent_3685_);
v___x_3691_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3693_; 
lean_ctor_set_uint8(v___x_3691_, sizeof(void*)*2, v___x_3689_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3691_);
v___x_3693_ = v___x_3669_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
}
else
{
return v___y_3666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object* v_e_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(v_e_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_);
lean_dec(v_a_3786_);
lean_dec_ref(v_a_3785_);
lean_dec(v_a_3784_);
lean_dec_ref(v_a_3783_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
return v_res_3788_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___closed__0(void){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3789_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3790_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___closed__0);
v___x_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg(lean_object* v_methods_3792_, lean_object* v_config_3793_, lean_object* v_hyp_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
lean_object* v___x_3803_; lean_object* v_rewriteSimpCache_3804_; lean_object* v_rewriteDSimpCache_3805_; lean_object* v_acCache_3806_; lean_object* v_typeAnalysis_3807_; lean_object* v_target_3808_; lean_object* v_hypotheses_3809_; uint8_t v_didChange_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3853_; 
v___x_3803_ = lean_st_ref_take(v_a_3795_);
v_rewriteSimpCache_3804_ = lean_ctor_get(v___x_3803_, 0);
v_rewriteDSimpCache_3805_ = lean_ctor_get(v___x_3803_, 1);
v_acCache_3806_ = lean_ctor_get(v___x_3803_, 2);
v_typeAnalysis_3807_ = lean_ctor_get(v___x_3803_, 3);
v_target_3808_ = lean_ctor_get(v___x_3803_, 4);
v_hypotheses_3809_ = lean_ctor_get(v___x_3803_, 5);
v_didChange_3810_ = lean_ctor_get_uint8(v___x_3803_, sizeof(void*)*6);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3812_ = v___x_3803_;
v_isShared_3813_ = v_isSharedCheck_3853_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_hypotheses_3809_);
lean_inc(v_target_3808_);
lean_inc(v_typeAnalysis_3807_);
lean_inc(v_acCache_3806_);
lean_inc(v_rewriteDSimpCache_3805_);
lean_inc(v_rewriteSimpCache_3804_);
lean_dec(v___x_3803_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3853_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3814_; lean_object* v___x_3816_; 
v___x_3814_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___closed__1);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 2, v___x_3814_);
v___x_3816_ = v___x_3812_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_rewriteSimpCache_3804_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v_rewriteDSimpCache_3805_);
lean_ctor_set(v_reuseFailAlloc_3852_, 2, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3852_, 3, v_typeAnalysis_3807_);
lean_ctor_set(v_reuseFailAlloc_3852_, 4, v_target_3808_);
lean_ctor_set(v_reuseFailAlloc_3852_, 5, v_hypotheses_3809_);
lean_ctor_set_uint8(v_reuseFailAlloc_3852_, sizeof(void*)*6, v_didChange_3810_);
v___x_3816_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
lean_object* v___x_3817_; lean_object* v_type_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3817_ = lean_st_ref_set(v_a_3795_, v___x_3816_);
v_type_3818_ = lean_ctor_get(v_hyp_3794_, 1);
v___x_3819_ = lean_unsigned_to_nat(0u);
v___x_3820_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
lean_ctor_set(v___x_3820_, 1, v_acCache_3806_);
lean_ctor_set(v___x_3820_, 2, v___x_3814_);
lean_ctor_set(v___x_3820_, 3, v___x_3814_);
lean_inc_ref(v_type_3818_);
v___x_3821_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3821_, 0, v_type_3818_);
v___x_3822_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_3821_, v_methods_3792_, v_config_3793_, v___x_3820_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v_fst_3824_; lean_object* v_snd_3825_; lean_object* v___x_3826_; lean_object* v_persistentCache_3827_; lean_object* v_rewriteSimpCache_3828_; lean_object* v_rewriteDSimpCache_3829_; lean_object* v_typeAnalysis_3830_; lean_object* v_target_3831_; lean_object* v_hypotheses_3832_; uint8_t v_didChange_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3842_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_a_3823_);
lean_dec_ref_known(v___x_3822_, 1);
v_fst_3824_ = lean_ctor_get(v_a_3823_, 0);
lean_inc(v_fst_3824_);
v_snd_3825_ = lean_ctor_get(v_a_3823_, 1);
lean_inc(v_snd_3825_);
lean_dec(v_a_3823_);
v___x_3826_ = lean_st_ref_take(v_a_3795_);
v_persistentCache_3827_ = lean_ctor_get(v_snd_3825_, 1);
lean_inc_ref(v_persistentCache_3827_);
lean_dec(v_snd_3825_);
v_rewriteSimpCache_3828_ = lean_ctor_get(v___x_3826_, 0);
v_rewriteDSimpCache_3829_ = lean_ctor_get(v___x_3826_, 1);
v_typeAnalysis_3830_ = lean_ctor_get(v___x_3826_, 3);
v_target_3831_ = lean_ctor_get(v___x_3826_, 4);
v_hypotheses_3832_ = lean_ctor_get(v___x_3826_, 5);
v_didChange_3833_ = lean_ctor_get_uint8(v___x_3826_, sizeof(void*)*6);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3842_ == 0)
{
lean_object* v_unused_3843_; 
v_unused_3843_ = lean_ctor_get(v___x_3826_, 2);
lean_dec(v_unused_3843_);
v___x_3835_ = v___x_3826_;
v_isShared_3836_ = v_isSharedCheck_3842_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_hypotheses_3832_);
lean_inc(v_target_3831_);
lean_inc(v_typeAnalysis_3830_);
lean_inc(v_rewriteDSimpCache_3829_);
lean_inc(v_rewriteSimpCache_3828_);
lean_dec(v___x_3826_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3842_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 2, v_persistentCache_3827_);
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_rewriteSimpCache_3828_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_rewriteDSimpCache_3829_);
lean_ctor_set(v_reuseFailAlloc_3841_, 2, v_persistentCache_3827_);
lean_ctor_set(v_reuseFailAlloc_3841_, 3, v_typeAnalysis_3830_);
lean_ctor_set(v_reuseFailAlloc_3841_, 4, v_target_3831_);
lean_ctor_set(v_reuseFailAlloc_3841_, 5, v_hypotheses_3832_);
lean_ctor_set_uint8(v_reuseFailAlloc_3841_, sizeof(void*)*6, v_didChange_3833_);
v___x_3838_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3839_ = lean_st_ref_set(v_a_3795_, v___x_3838_);
v___x_3840_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_3794_, v_fst_3824_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
return v___x_3840_;
}
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec_ref(v_hyp_3794_);
v_a_3844_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3822_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3822_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg___boxed(lean_object* v_methods_3854_, lean_object* v_config_3855_, lean_object* v_hyp_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg(v_methods_3854_, v_config_3855_, v_hyp_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
lean_dec_ref(v_a_3858_);
lean_dec(v_a_3857_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp(lean_object* v_methods_3866_, lean_object* v_config_3867_, lean_object* v_hyp_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg(v_methods_3866_, v_config_3867_, v_hyp_3868_, v_a_3870_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___boxed(lean_object* v_methods_3882_, lean_object* v_config_3883_, lean_object* v_hyp_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp(v_methods_3882_, v_config_3883_, v_hyp_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
lean_dec(v_a_3895_);
lean_dec_ref(v_a_3894_);
lean_dec(v_a_3893_);
lean_dec_ref(v_a_3892_);
lean_dec(v_a_3891_);
lean_dec_ref(v_a_3890_);
lean_dec(v_a_3889_);
lean_dec_ref(v_a_3888_);
lean_dec(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec_ref(v_a_3885_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg___lam__0(lean_object* v_x_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v___x_3911_; 
lean_inc(v___y_3905_);
lean_inc_ref(v___y_3904_);
lean_inc(v___y_3903_);
lean_inc_ref(v___y_3902_);
lean_inc(v___y_3901_);
lean_inc(v___y_3900_);
lean_inc_ref(v___y_3899_);
v___x_3911_ = lean_apply_12(v_x_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, lean_box(0));
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg___lam__0___boxed(lean_object* v_x_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg___lam__0(v_x_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(lean_object* v_mvarId_3926_, lean_object* v_x_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v___f_3940_; lean_object* v___x_3941_; 
lean_inc(v___y_3934_);
lean_inc_ref(v___y_3933_);
lean_inc(v___y_3932_);
lean_inc_ref(v___y_3931_);
lean_inc(v___y_3930_);
lean_inc(v___y_3929_);
lean_inc_ref(v___y_3928_);
v___f_3940_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_3940_, 0, v_x_3927_);
lean_closure_set(v___f_3940_, 1, v___y_3928_);
lean_closure_set(v___f_3940_, 2, v___y_3929_);
lean_closure_set(v___f_3940_, 3, v___y_3930_);
lean_closure_set(v___f_3940_, 4, v___y_3931_);
lean_closure_set(v___f_3940_, 5, v___y_3932_);
lean_closure_set(v___f_3940_, 6, v___y_3933_);
lean_closure_set(v___f_3940_, 7, v___y_3934_);
v___x_3941_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3926_, v___f_3940_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
if (lean_obj_tag(v___x_3941_) == 0)
{
return v___x_3941_;
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3941_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3941_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg___boxed(lean_object* v_mvarId_3950_, lean_object* v_x_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(v_mvarId_3950_, v_x_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3(lean_object* v_00_u03b1_3965_, lean_object* v_mvarId_3966_, lean_object* v_x_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v___x_3980_; 
v___x_3980_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(v_mvarId_3966_, v_x_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___boxed(lean_object* v_00_u03b1_3981_, lean_object* v_mvarId_3982_, lean_object* v_x_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3(v_00_u03b1_3981_, v_mvarId_3982_, v_x_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(lean_object* v_x_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed(lean_object* v_x_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(v_x_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v_x_4010_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__2(uint8_t v___x_4022_, lean_object* v___f_4023_, lean_object* v_____r_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v___x_4037_; lean_object* v_rewriteSimpCache_4038_; lean_object* v_rewriteDSimpCache_4039_; lean_object* v_acCache_4040_; lean_object* v_typeAnalysis_4041_; lean_object* v_target_4042_; lean_object* v_hypotheses_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4053_; 
v___x_4037_ = lean_st_ref_take(v___y_4026_);
v_rewriteSimpCache_4038_ = lean_ctor_get(v___x_4037_, 0);
v_rewriteDSimpCache_4039_ = lean_ctor_get(v___x_4037_, 1);
v_acCache_4040_ = lean_ctor_get(v___x_4037_, 2);
v_typeAnalysis_4041_ = lean_ctor_get(v___x_4037_, 3);
v_target_4042_ = lean_ctor_get(v___x_4037_, 4);
v_hypotheses_4043_ = lean_ctor_get(v___x_4037_, 5);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4045_ = v___x_4037_;
v_isShared_4046_ = v_isSharedCheck_4053_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_hypotheses_4043_);
lean_inc(v_target_4042_);
lean_inc(v_typeAnalysis_4041_);
lean_inc(v_acCache_4040_);
lean_inc(v_rewriteDSimpCache_4039_);
lean_inc(v_rewriteSimpCache_4038_);
lean_dec(v___x_4037_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4053_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_rewriteSimpCache_4038_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v_rewriteDSimpCache_4039_);
lean_ctor_set(v_reuseFailAlloc_4052_, 2, v_acCache_4040_);
lean_ctor_set(v_reuseFailAlloc_4052_, 3, v_typeAnalysis_4041_);
lean_ctor_set(v_reuseFailAlloc_4052_, 4, v_target_4042_);
lean_ctor_set(v_reuseFailAlloc_4052_, 5, v_hypotheses_4043_);
v___x_4048_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
lean_ctor_set_uint8(v___x_4048_, sizeof(void*)*6, v___x_4022_);
v___x_4049_ = lean_st_ref_set(v___y_4026_, v___x_4048_);
v___x_4050_ = lean_box(0);
lean_inc(v___y_4035_);
lean_inc_ref(v___y_4034_);
lean_inc(v___y_4033_);
lean_inc_ref(v___y_4032_);
lean_inc(v___y_4031_);
lean_inc_ref(v___y_4030_);
lean_inc(v___y_4029_);
lean_inc_ref(v___y_4028_);
lean_inc(v___y_4027_);
lean_inc(v___y_4026_);
lean_inc_ref(v___y_4025_);
v___x_4051_ = lean_apply_13(v___f_4023_, v___x_4050_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, lean_box(0));
return v___x_4051_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__2___boxed(lean_object* v___x_4054_, lean_object* v___f_4055_, lean_object* v_____r_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
uint8_t v___x_33947__boxed_4069_; lean_object* v_res_4070_; 
v___x_33947__boxed_4069_ = lean_unbox(v___x_4054_);
v_res_4070_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__2(v___x_33947__boxed_4069_, v___f_4055_, v_____r_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_cls_4071_, lean_object* v_msg_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v_ref_4078_; lean_object* v___x_4079_; lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4124_; 
v_ref_4078_ = lean_ctor_get(v___y_4075_, 5);
v___x_4079_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4082_ = v___x_4079_;
v_isShared_4083_ = v_isSharedCheck_4124_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4079_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4124_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4084_; lean_object* v_traceState_4085_; lean_object* v_env_4086_; lean_object* v_nextMacroScope_4087_; lean_object* v_ngen_4088_; lean_object* v_auxDeclNGen_4089_; lean_object* v_cache_4090_; lean_object* v_messages_4091_; lean_object* v_infoState_4092_; lean_object* v_snapshotTasks_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4123_; 
v___x_4084_ = lean_st_ref_take(v___y_4076_);
v_traceState_4085_ = lean_ctor_get(v___x_4084_, 4);
v_env_4086_ = lean_ctor_get(v___x_4084_, 0);
v_nextMacroScope_4087_ = lean_ctor_get(v___x_4084_, 1);
v_ngen_4088_ = lean_ctor_get(v___x_4084_, 2);
v_auxDeclNGen_4089_ = lean_ctor_get(v___x_4084_, 3);
v_cache_4090_ = lean_ctor_get(v___x_4084_, 5);
v_messages_4091_ = lean_ctor_get(v___x_4084_, 6);
v_infoState_4092_ = lean_ctor_get(v___x_4084_, 7);
v_snapshotTasks_4093_ = lean_ctor_get(v___x_4084_, 8);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4095_ = v___x_4084_;
v_isShared_4096_ = v_isSharedCheck_4123_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_snapshotTasks_4093_);
lean_inc(v_infoState_4092_);
lean_inc(v_messages_4091_);
lean_inc(v_cache_4090_);
lean_inc(v_traceState_4085_);
lean_inc(v_auxDeclNGen_4089_);
lean_inc(v_ngen_4088_);
lean_inc(v_nextMacroScope_4087_);
lean_inc(v_env_4086_);
lean_dec(v___x_4084_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4123_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
uint64_t v_tid_4097_; lean_object* v_traces_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4122_; 
v_tid_4097_ = lean_ctor_get_uint64(v_traceState_4085_, sizeof(void*)*1);
v_traces_4098_ = lean_ctor_get(v_traceState_4085_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v_traceState_4085_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4100_ = v_traceState_4085_;
v_isShared_4101_ = v_isSharedCheck_4122_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_traces_4098_);
lean_dec(v_traceState_4085_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4122_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4102_; double v___x_4103_; uint8_t v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4112_; 
v___x_4102_ = lean_box(0);
v___x_4103_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_4104_ = 0;
v___x_4105_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_4106_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4106_, 0, v_cls_4071_);
lean_ctor_set(v___x_4106_, 1, v___x_4102_);
lean_ctor_set(v___x_4106_, 2, v___x_4105_);
lean_ctor_set_float(v___x_4106_, sizeof(void*)*3, v___x_4103_);
lean_ctor_set_float(v___x_4106_, sizeof(void*)*3 + 8, v___x_4103_);
lean_ctor_set_uint8(v___x_4106_, sizeof(void*)*3 + 16, v___x_4104_);
v___x_4107_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_4108_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4106_);
lean_ctor_set(v___x_4108_, 1, v_a_4080_);
lean_ctor_set(v___x_4108_, 2, v___x_4107_);
lean_inc(v_ref_4078_);
v___x_4109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4109_, 0, v_ref_4078_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
v___x_4110_ = l_Lean_PersistentArray_push___redArg(v_traces_4098_, v___x_4109_);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v___x_4110_);
v___x_4112_ = v___x_4100_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___x_4110_);
lean_ctor_set_uint64(v_reuseFailAlloc_4121_, sizeof(void*)*1, v_tid_4097_);
v___x_4112_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
lean_object* v___x_4114_; 
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 4, v___x_4112_);
v___x_4114_ = v___x_4095_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_env_4086_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v_nextMacroScope_4087_);
lean_ctor_set(v_reuseFailAlloc_4120_, 2, v_ngen_4088_);
lean_ctor_set(v_reuseFailAlloc_4120_, 3, v_auxDeclNGen_4089_);
lean_ctor_set(v_reuseFailAlloc_4120_, 4, v___x_4112_);
lean_ctor_set(v_reuseFailAlloc_4120_, 5, v_cache_4090_);
lean_ctor_set(v_reuseFailAlloc_4120_, 6, v_messages_4091_);
lean_ctor_set(v_reuseFailAlloc_4120_, 7, v_infoState_4092_);
lean_ctor_set(v_reuseFailAlloc_4120_, 8, v_snapshotTasks_4093_);
v___x_4114_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4118_; 
v___x_4115_ = lean_st_ref_set(v___y_4076_, v___x_4114_);
v___x_4116_ = lean_box(0);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 0, v___x_4116_);
v___x_4118_ = v___x_4082_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4116_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_cls_4125_, lean_object* v_msg_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_4125_, v_msg_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_x_4133_, lean_object* v_x_4134_, lean_object* v_x_4135_, lean_object* v_x_4136_){
_start:
{
lean_object* v_ks_4137_; lean_object* v_vs_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4162_; 
v_ks_4137_ = lean_ctor_get(v_x_4133_, 0);
v_vs_4138_ = lean_ctor_get(v_x_4133_, 1);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_x_4133_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4140_ = v_x_4133_;
v_isShared_4141_ = v_isSharedCheck_4162_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_vs_4138_);
lean_inc(v_ks_4137_);
lean_dec(v_x_4133_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4162_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4142_; uint8_t v___x_4143_; 
v___x_4142_ = lean_array_get_size(v_ks_4137_);
v___x_4143_ = lean_nat_dec_lt(v_x_4134_, v___x_4142_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4147_; 
lean_dec(v_x_4134_);
v___x_4144_ = lean_array_push(v_ks_4137_, v_x_4135_);
v___x_4145_ = lean_array_push(v_vs_4138_, v_x_4136_);
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 1, v___x_4145_);
lean_ctor_set(v___x_4140_, 0, v___x_4144_);
v___x_4147_ = v___x_4140_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4144_);
lean_ctor_set(v_reuseFailAlloc_4148_, 1, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
else
{
lean_object* v_k_x27_4149_; uint8_t v___x_4150_; 
v_k_x27_4149_ = lean_array_fget_borrowed(v_ks_4137_, v_x_4134_);
v___x_4150_ = l_Lean_instBEqMVarId_beq(v_x_4135_, v_k_x27_4149_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4152_; 
if (v_isShared_4141_ == 0)
{
v___x_4152_ = v___x_4140_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_ks_4137_);
lean_ctor_set(v_reuseFailAlloc_4156_, 1, v_vs_4138_);
v___x_4152_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4153_ = lean_unsigned_to_nat(1u);
v___x_4154_ = lean_nat_add(v_x_4134_, v___x_4153_);
lean_dec(v_x_4134_);
v_x_4133_ = v___x_4152_;
v_x_4134_ = v___x_4154_;
goto _start;
}
}
else
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4160_; 
v___x_4157_ = lean_array_fset(v_ks_4137_, v_x_4134_, v_x_4135_);
v___x_4158_ = lean_array_fset(v_vs_4138_, v_x_4134_, v_x_4136_);
lean_dec(v_x_4134_);
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 1, v___x_4158_);
lean_ctor_set(v___x_4140_, 0, v___x_4157_);
v___x_4160_ = v___x_4140_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4157_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_n_4163_, lean_object* v_k_4164_, lean_object* v_v_4165_){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4166_ = lean_unsigned_to_nat(0u);
v___x_4167_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(v_n_4163_, v___x_4166_, v_k_4164_, v_v_4165_);
return v___x_4167_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4168_; 
v___x_4168_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg(lean_object* v_x_4169_, size_t v_x_4170_, size_t v_x_4171_, lean_object* v_x_4172_, lean_object* v_x_4173_){
_start:
{
if (lean_obj_tag(v_x_4169_) == 0)
{
lean_object* v_es_4174_; size_t v___x_4175_; size_t v___x_4176_; lean_object* v_j_4177_; lean_object* v___x_4178_; uint8_t v___x_4179_; 
v_es_4174_ = lean_ctor_get(v_x_4169_, 0);
v___x_4175_ = ((size_t)31ULL);
v___x_4176_ = lean_usize_land(v_x_4170_, v___x_4175_);
v_j_4177_ = lean_usize_to_nat(v___x_4176_);
v___x_4178_ = lean_array_get_size(v_es_4174_);
v___x_4179_ = lean_nat_dec_lt(v_j_4177_, v___x_4178_);
if (v___x_4179_ == 0)
{
lean_dec(v_j_4177_);
lean_dec(v_x_4173_);
lean_dec(v_x_4172_);
return v_x_4169_;
}
else
{
lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4218_; 
lean_inc_ref(v_es_4174_);
v_isSharedCheck_4218_ = !lean_is_exclusive(v_x_4169_);
if (v_isSharedCheck_4218_ == 0)
{
lean_object* v_unused_4219_; 
v_unused_4219_ = lean_ctor_get(v_x_4169_, 0);
lean_dec(v_unused_4219_);
v___x_4181_ = v_x_4169_;
v_isShared_4182_ = v_isSharedCheck_4218_;
goto v_resetjp_4180_;
}
else
{
lean_dec(v_x_4169_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4218_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v_v_4183_; lean_object* v___x_4184_; lean_object* v_xs_x27_4185_; lean_object* v___y_4187_; 
v_v_4183_ = lean_array_fget(v_es_4174_, v_j_4177_);
v___x_4184_ = lean_box(0);
v_xs_x27_4185_ = lean_array_fset(v_es_4174_, v_j_4177_, v___x_4184_);
switch(lean_obj_tag(v_v_4183_))
{
case 0:
{
lean_object* v_key_4192_; lean_object* v_val_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4203_; 
v_key_4192_ = lean_ctor_get(v_v_4183_, 0);
v_val_4193_ = lean_ctor_get(v_v_4183_, 1);
v_isSharedCheck_4203_ = !lean_is_exclusive(v_v_4183_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4195_ = v_v_4183_;
v_isShared_4196_ = v_isSharedCheck_4203_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_val_4193_);
lean_inc(v_key_4192_);
lean_dec(v_v_4183_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4203_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
uint8_t v___x_4197_; 
v___x_4197_ = l_Lean_instBEqMVarId_beq(v_x_4172_, v_key_4192_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
lean_del_object(v___x_4195_);
v___x_4198_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4192_, v_val_4193_, v_x_4172_, v_x_4173_);
v___x_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
v___y_4187_ = v___x_4199_;
goto v___jp_4186_;
}
else
{
lean_object* v___x_4201_; 
lean_dec(v_val_4193_);
lean_dec(v_key_4192_);
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 1, v_x_4173_);
lean_ctor_set(v___x_4195_, 0, v_x_4172_);
v___x_4201_ = v___x_4195_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_x_4172_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v_x_4173_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
v___y_4187_ = v___x_4201_;
goto v___jp_4186_;
}
}
}
}
case 1:
{
lean_object* v_node_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4216_; 
v_node_4204_ = lean_ctor_get(v_v_4183_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v_v_4183_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4206_ = v_v_4183_;
v_isShared_4207_ = v_isSharedCheck_4216_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_node_4204_);
lean_dec(v_v_4183_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4216_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
size_t v___x_4208_; size_t v___x_4209_; size_t v___x_4210_; size_t v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4214_; 
v___x_4208_ = ((size_t)5ULL);
v___x_4209_ = lean_usize_shift_right(v_x_4170_, v___x_4208_);
v___x_4210_ = ((size_t)1ULL);
v___x_4211_ = lean_usize_add(v_x_4171_, v___x_4210_);
v___x_4212_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg(v_node_4204_, v___x_4209_, v___x_4211_, v_x_4172_, v_x_4173_);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v___x_4212_);
v___x_4214_ = v___x_4206_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v___x_4212_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
v___y_4187_ = v___x_4214_;
goto v___jp_4186_;
}
}
}
default: 
{
lean_object* v___x_4217_; 
v___x_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4217_, 0, v_x_4172_);
lean_ctor_set(v___x_4217_, 1, v_x_4173_);
v___y_4187_ = v___x_4217_;
goto v___jp_4186_;
}
}
v___jp_4186_:
{
lean_object* v___x_4188_; lean_object* v___x_4190_; 
v___x_4188_ = lean_array_fset(v_xs_x27_4185_, v_j_4177_, v___y_4187_);
lean_dec(v_j_4177_);
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 0, v___x_4188_);
v___x_4190_ = v___x_4181_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4188_);
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
else
{
lean_object* v_ks_4220_; lean_object* v_vs_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4241_; 
v_ks_4220_ = lean_ctor_get(v_x_4169_, 0);
v_vs_4221_ = lean_ctor_get(v_x_4169_, 1);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_x_4169_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4223_ = v_x_4169_;
v_isShared_4224_ = v_isSharedCheck_4241_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_vs_4221_);
lean_inc(v_ks_4220_);
lean_dec(v_x_4169_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4241_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_ks_4220_);
lean_ctor_set(v_reuseFailAlloc_4240_, 1, v_vs_4221_);
v___x_4226_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
lean_object* v_newNode_4227_; uint8_t v___y_4229_; size_t v___x_4235_; uint8_t v___x_4236_; 
v_newNode_4227_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__5___redArg(v___x_4226_, v_x_4172_, v_x_4173_);
v___x_4235_ = ((size_t)7ULL);
v___x_4236_ = lean_usize_dec_le(v___x_4235_, v_x_4171_);
if (v___x_4236_ == 0)
{
lean_object* v___x_4237_; lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4237_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4227_);
v___x_4238_ = lean_unsigned_to_nat(4u);
v___x_4239_ = lean_nat_dec_lt(v___x_4237_, v___x_4238_);
lean_dec(v___x_4237_);
v___y_4229_ = v___x_4239_;
goto v___jp_4228_;
}
else
{
v___y_4229_ = v___x_4236_;
goto v___jp_4228_;
}
v___jp_4228_:
{
if (v___y_4229_ == 0)
{
lean_object* v_ks_4230_; lean_object* v_vs_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v_ks_4230_ = lean_ctor_get(v_newNode_4227_, 0);
lean_inc_ref(v_ks_4230_);
v_vs_4231_ = lean_ctor_get(v_newNode_4227_, 1);
lean_inc_ref(v_vs_4231_);
lean_dec_ref(v_newNode_4227_);
v___x_4232_ = lean_unsigned_to_nat(0u);
v___x_4233_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_4234_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__6___redArg(v_x_4171_, v_ks_4230_, v_vs_4231_, v___x_4232_, v___x_4233_);
lean_dec_ref(v_vs_4231_);
lean_dec_ref(v_ks_4230_);
return v___x_4234_;
}
else
{
return v_newNode_4227_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__6___redArg(size_t v_depth_4242_, lean_object* v_keys_4243_, lean_object* v_vals_4244_, lean_object* v_i_4245_, lean_object* v_entries_4246_){
_start:
{
lean_object* v___x_4247_; uint8_t v___x_4248_; 
v___x_4247_ = lean_array_get_size(v_keys_4243_);
v___x_4248_ = lean_nat_dec_lt(v_i_4245_, v___x_4247_);
if (v___x_4248_ == 0)
{
lean_dec(v_i_4245_);
return v_entries_4246_;
}
else
{
lean_object* v_k_4249_; lean_object* v_v_4250_; uint64_t v___x_4251_; size_t v_h_4252_; size_t v___x_4253_; lean_object* v___x_4254_; size_t v___x_4255_; size_t v___x_4256_; size_t v___x_4257_; size_t v_h_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v_k_4249_ = lean_array_fget_borrowed(v_keys_4243_, v_i_4245_);
v_v_4250_ = lean_array_fget_borrowed(v_vals_4244_, v_i_4245_);
v___x_4251_ = l_Lean_instHashableMVarId_hash(v_k_4249_);
v_h_4252_ = lean_uint64_to_usize(v___x_4251_);
v___x_4253_ = ((size_t)5ULL);
v___x_4254_ = lean_unsigned_to_nat(1u);
v___x_4255_ = ((size_t)1ULL);
v___x_4256_ = lean_usize_sub(v_depth_4242_, v___x_4255_);
v___x_4257_ = lean_usize_mul(v___x_4253_, v___x_4256_);
v_h_4258_ = lean_usize_shift_right(v_h_4252_, v___x_4257_);
v___x_4259_ = lean_nat_add(v_i_4245_, v___x_4254_);
lean_dec(v_i_4245_);
lean_inc(v_v_4250_);
lean_inc(v_k_4249_);
v___x_4260_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg(v_entries_4246_, v_h_4258_, v_depth_4242_, v_k_4249_, v_v_4250_);
v_i_4245_ = v___x_4259_;
v_entries_4246_ = v___x_4260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_depth_4262_, lean_object* v_keys_4263_, lean_object* v_vals_4264_, lean_object* v_i_4265_, lean_object* v_entries_4266_){
_start:
{
size_t v_depth_boxed_4267_; lean_object* v_res_4268_; 
v_depth_boxed_4267_ = lean_unbox_usize(v_depth_4262_);
lean_dec(v_depth_4262_);
v_res_4268_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__6___redArg(v_depth_boxed_4267_, v_keys_4263_, v_vals_4264_, v_i_4265_, v_entries_4266_);
lean_dec_ref(v_vals_4264_);
lean_dec_ref(v_keys_4263_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_4269_, lean_object* v_x_4270_, lean_object* v_x_4271_, lean_object* v_x_4272_, lean_object* v_x_4273_){
_start:
{
size_t v_x_34183__boxed_4274_; size_t v_x_34184__boxed_4275_; lean_object* v_res_4276_; 
v_x_34183__boxed_4274_ = lean_unbox_usize(v_x_4270_);
lean_dec(v_x_4270_);
v_x_34184__boxed_4275_ = lean_unbox_usize(v_x_4271_);
lean_dec(v_x_4271_);
v_res_4276_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg(v_x_4269_, v_x_34183__boxed_4274_, v_x_34184__boxed_4275_, v_x_4272_, v_x_4273_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1___redArg(lean_object* v_x_4277_, lean_object* v_x_4278_, lean_object* v_x_4279_){
_start:
{
uint64_t v___x_4280_; size_t v___x_4281_; size_t v___x_4282_; lean_object* v___x_4283_; 
v___x_4280_ = l_Lean_instHashableMVarId_hash(v_x_4278_);
v___x_4281_ = lean_uint64_to_usize(v___x_4280_);
v___x_4282_ = ((size_t)1ULL);
v___x_4283_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg(v_x_4277_, v___x_4281_, v___x_4282_, v_x_4278_, v_x_4279_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_mvarId_4284_, lean_object* v_val_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v___x_4288_; lean_object* v_mctx_4289_; lean_object* v_cache_4290_; lean_object* v_zetaDeltaFVarIds_4291_; lean_object* v_postponed_4292_; lean_object* v_diag_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4321_; 
v___x_4288_ = lean_st_ref_take(v___y_4286_);
v_mctx_4289_ = lean_ctor_get(v___x_4288_, 0);
v_cache_4290_ = lean_ctor_get(v___x_4288_, 1);
v_zetaDeltaFVarIds_4291_ = lean_ctor_get(v___x_4288_, 2);
v_postponed_4292_ = lean_ctor_get(v___x_4288_, 3);
v_diag_4293_ = lean_ctor_get(v___x_4288_, 4);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4295_ = v___x_4288_;
v_isShared_4296_ = v_isSharedCheck_4321_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_diag_4293_);
lean_inc(v_postponed_4292_);
lean_inc(v_zetaDeltaFVarIds_4291_);
lean_inc(v_cache_4290_);
lean_inc(v_mctx_4289_);
lean_dec(v___x_4288_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4321_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v_depth_4297_; lean_object* v_levelAssignDepth_4298_; lean_object* v_lmvarCounter_4299_; lean_object* v_mvarCounter_4300_; lean_object* v_lDecls_4301_; lean_object* v_decls_4302_; lean_object* v_userNames_4303_; lean_object* v_lAssignment_4304_; lean_object* v_eAssignment_4305_; lean_object* v_dAssignment_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4320_; 
v_depth_4297_ = lean_ctor_get(v_mctx_4289_, 0);
v_levelAssignDepth_4298_ = lean_ctor_get(v_mctx_4289_, 1);
v_lmvarCounter_4299_ = lean_ctor_get(v_mctx_4289_, 2);
v_mvarCounter_4300_ = lean_ctor_get(v_mctx_4289_, 3);
v_lDecls_4301_ = lean_ctor_get(v_mctx_4289_, 4);
v_decls_4302_ = lean_ctor_get(v_mctx_4289_, 5);
v_userNames_4303_ = lean_ctor_get(v_mctx_4289_, 6);
v_lAssignment_4304_ = lean_ctor_get(v_mctx_4289_, 7);
v_eAssignment_4305_ = lean_ctor_get(v_mctx_4289_, 8);
v_dAssignment_4306_ = lean_ctor_get(v_mctx_4289_, 9);
v_isSharedCheck_4320_ = !lean_is_exclusive(v_mctx_4289_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4308_ = v_mctx_4289_;
v_isShared_4309_ = v_isSharedCheck_4320_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_dAssignment_4306_);
lean_inc(v_eAssignment_4305_);
lean_inc(v_lAssignment_4304_);
lean_inc(v_userNames_4303_);
lean_inc(v_decls_4302_);
lean_inc(v_lDecls_4301_);
lean_inc(v_mvarCounter_4300_);
lean_inc(v_lmvarCounter_4299_);
lean_inc(v_levelAssignDepth_4298_);
lean_inc(v_depth_4297_);
lean_dec(v_mctx_4289_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4320_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4310_; lean_object* v___x_4312_; 
v___x_4310_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1___redArg(v_eAssignment_4305_, v_mvarId_4284_, v_val_4285_);
if (v_isShared_4309_ == 0)
{
lean_ctor_set(v___x_4308_, 8, v___x_4310_);
v___x_4312_ = v___x_4308_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_depth_4297_);
lean_ctor_set(v_reuseFailAlloc_4319_, 1, v_levelAssignDepth_4298_);
lean_ctor_set(v_reuseFailAlloc_4319_, 2, v_lmvarCounter_4299_);
lean_ctor_set(v_reuseFailAlloc_4319_, 3, v_mvarCounter_4300_);
lean_ctor_set(v_reuseFailAlloc_4319_, 4, v_lDecls_4301_);
lean_ctor_set(v_reuseFailAlloc_4319_, 5, v_decls_4302_);
lean_ctor_set(v_reuseFailAlloc_4319_, 6, v_userNames_4303_);
lean_ctor_set(v_reuseFailAlloc_4319_, 7, v_lAssignment_4304_);
lean_ctor_set(v_reuseFailAlloc_4319_, 8, v___x_4310_);
lean_ctor_set(v_reuseFailAlloc_4319_, 9, v_dAssignment_4306_);
v___x_4312_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
lean_object* v___x_4314_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4312_);
v___x_4314_ = v___x_4295_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v___x_4312_);
lean_ctor_set(v_reuseFailAlloc_4318_, 1, v_cache_4290_);
lean_ctor_set(v_reuseFailAlloc_4318_, 2, v_zetaDeltaFVarIds_4291_);
lean_ctor_set(v_reuseFailAlloc_4318_, 3, v_postponed_4292_);
lean_ctor_set(v_reuseFailAlloc_4318_, 4, v_diag_4293_);
v___x_4314_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4315_ = lean_st_ref_set(v___y_4286_, v___x_4314_);
v___x_4316_ = lean_box(0);
v___x_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4316_);
return v___x_4317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___boxed(lean_object* v_mvarId_4322_, lean_object* v_val_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_mvarId_4322_, v_val_4323_, v___y_4324_);
lean_dec(v___y_4324_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__1(lean_object* v_snd_4327_, lean_object* v_a_4328_, lean_object* v___x_4329_, lean_object* v_____r_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4343_ = lean_array_push(v_snd_4327_, v_a_4328_);
v___x_4344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4329_);
lean_ctor_set(v___x_4344_, 1, v___x_4343_);
v___x_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4344_);
v___x_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4346_, 0, v___x_4345_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__1___boxed(lean_object* v_snd_4347_, lean_object* v_a_4348_, lean_object* v___x_4349_, lean_object* v_____r_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__1(v_snd_4347_, v_a_4348_, v___x_4349_, v_____r_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
return v_res_4363_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4365_; lean_object* v___f_4366_; lean_object* v_methods_4367_; 
v___x_4365_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 11, 0);
v___f_4366_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__0));
v_methods_4367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_methods_4367_, 0, v___f_4366_);
lean_ctor_set(v_methods_4367_, 1, v___x_4365_);
return v_methods_4367_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4369_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__2));
v___x_4370_ = l_Lean_stringToMessageData(v___x_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_upperBound_4371_, lean_object* v___x_4372_, lean_object* v_config_4373_, lean_object* v_a_4374_, lean_object* v_b_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v___y_4389_; uint8_t v___x_4411_; 
v___x_4411_ = lean_nat_dec_lt(v_a_4374_, v_upperBound_4371_);
if (v___x_4411_ == 0)
{
lean_object* v___x_4412_; 
lean_dec(v_a_4374_);
lean_dec_ref(v_config_4373_);
v___x_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4412_, 0, v_b_4375_);
return v___x_4412_;
}
else
{
lean_object* v_methods_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v_methods_4413_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__1);
v___x_4414_ = lean_array_fget_borrowed(v___x_4372_, v_a_4374_);
lean_inc(v___x_4414_);
lean_inc_ref(v_config_4373_);
v___x_4415_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_simp___redArg(v_methods_4413_, v_config_4373_, v___x_4414_, v___y_4377_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; lean_object* v_snd_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4482_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4416_);
lean_dec_ref_known(v___x_4415_, 1);
v_snd_4417_ = lean_ctor_get(v_b_4375_, 1);
v_isSharedCheck_4482_ = !lean_is_exclusive(v_b_4375_);
if (v_isSharedCheck_4482_ == 0)
{
lean_object* v_unused_4483_; 
v_unused_4483_ = lean_ctor_get(v_b_4375_, 0);
lean_dec(v_unused_4483_);
v___x_4419_ = v_b_4375_;
v_isShared_4420_ = v_isSharedCheck_4482_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_snd_4417_);
lean_dec(v_b_4375_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4482_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v_type_4421_; lean_object* v_value_4422_; uint8_t v___x_4423_; 
v_type_4421_ = lean_ctor_get(v_a_4416_, 1);
v_value_4422_ = lean_ctor_get(v_a_4416_, 2);
lean_inc_ref(v_type_4421_);
v___x_4423_ = l_Lean_Expr_isFalse(v_type_4421_);
if (v___x_4423_ == 0)
{
lean_object* v_type_4424_; lean_object* v___x_4425_; lean_object* v___f_4426_; uint8_t v___x_4454_; 
lean_del_object(v___x_4419_);
v_type_4424_ = lean_ctor_get(v___x_4414_, 1);
v___x_4425_ = lean_box(0);
lean_inc(v_a_4416_);
lean_inc(v_snd_4417_);
v___f_4426_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_4426_, 0, v_snd_4417_);
lean_closure_set(v___f_4426_, 1, v_a_4416_);
lean_closure_set(v___f_4426_, 2, v___x_4425_);
v___x_4454_ = lean_expr_eqv(v_type_4424_, v_type_4421_);
if (v___x_4454_ == 0)
{
lean_inc_ref(v_type_4421_);
lean_dec(v_snd_4417_);
lean_dec(v_a_4416_);
goto v___jp_4430_;
}
else
{
if (v___x_4423_ == 0)
{
lean_object* v___x_4455_; lean_object* v___x_4456_; 
lean_dec_ref(v___f_4426_);
v___x_4455_ = lean_box(0);
v___x_4456_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__1(v_snd_4417_, v_a_4416_, v___x_4425_, v___x_4455_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
v___y_4389_ = v___x_4456_;
goto v___jp_4388_;
}
else
{
lean_inc_ref(v_type_4421_);
lean_dec(v_snd_4417_);
lean_dec(v_a_4416_);
goto v___jp_4430_;
}
}
v___jp_4427_:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4428_ = lean_box(0);
v___x_4429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__2(v___x_4411_, v___f_4426_, v___x_4428_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
v___y_4389_ = v___x_4429_;
goto v___jp_4388_;
}
v___jp_4430_:
{
lean_object* v_options_4431_; uint8_t v_hasTrace_4432_; 
v_options_4431_ = lean_ctor_get(v___y_4385_, 2);
v_hasTrace_4432_ = lean_ctor_get_uint8(v_options_4431_, sizeof(void*)*1);
if (v_hasTrace_4432_ == 0)
{
lean_dec_ref(v_type_4421_);
goto v___jp_4427_;
}
else
{
lean_object* v_inheritedTraceOptions_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; uint8_t v___x_4436_; 
v_inheritedTraceOptions_4433_ = lean_ctor_get(v___y_4385_, 13);
v___x_4434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_4435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_4436_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4433_, v_options_4431_, v___x_4435_);
if (v___x_4436_ == 0)
{
lean_dec_ref(v_type_4421_);
goto v___jp_4427_;
}
else
{
lean_object* v_type_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v_type_4437_ = lean_ctor_get(v___x_4414_, 1);
lean_inc_ref(v_type_4437_);
v___x_4438_ = l_Lean_MessageData_ofExpr(v_type_4437_);
v___x_4439_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___closed__3);
v___x_4440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4438_);
lean_ctor_set(v___x_4440_, 1, v___x_4439_);
v___x_4441_ = l_Lean_MessageData_ofExpr(v_type_4421_);
v___x_4442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4440_);
lean_ctor_set(v___x_4442_, 1, v___x_4441_);
v___x_4443_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v___x_4434_, v___x_4442_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v_a_4444_; lean_object* v___x_4445_; 
v_a_4444_ = lean_ctor_get(v___x_4443_, 0);
lean_inc(v_a_4444_);
lean_dec_ref_known(v___x_4443_, 1);
v___x_4445_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__2(v___x_4411_, v___f_4426_, v_a_4444_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
v___y_4389_ = v___x_4445_;
goto v___jp_4388_;
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec_ref(v___f_4426_);
lean_dec(v_a_4374_);
lean_dec_ref(v_config_4373_);
v_a_4446_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4443_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4443_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4457_; lean_object* v_target_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
lean_inc_ref(v_value_4422_);
lean_dec(v_a_4416_);
lean_dec(v_a_4374_);
lean_dec_ref(v_config_4373_);
v___x_4457_ = lean_st_ref_get(v___y_4377_);
v_target_4458_ = lean_ctor_get(v___x_4457_, 4);
lean_inc_ref(v_target_4458_);
lean_dec(v___x_4457_);
v___x_4459_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_4458_);
lean_dec_ref(v_target_4458_);
v___x_4460_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v___x_4459_, v_value_4422_, v___y_4384_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4472_; 
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4472_ == 0)
{
lean_object* v_unused_4473_; 
v_unused_4473_ = lean_ctor_get(v___x_4460_, 0);
lean_dec(v_unused_4473_);
v___x_4462_ = v___x_4460_;
v_isShared_4463_ = v_isSharedCheck_4472_;
goto v_resetjp_4461_;
}
else
{
lean_dec(v___x_4460_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4472_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4467_; 
v___x_4464_ = lean_box(v___x_4423_);
v___x_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4464_);
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 0, v___x_4465_);
v___x_4467_ = v___x_4419_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_snd_4417_);
v___x_4467_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
lean_object* v___x_4469_; 
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v___x_4467_);
v___x_4469_ = v___x_4462_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
lean_del_object(v___x_4419_);
lean_dec(v_snd_4417_);
v_a_4474_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4460_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4460_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
}
}
else
{
lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4491_; 
lean_dec_ref(v_b_4375_);
lean_dec(v_a_4374_);
lean_dec_ref(v_config_4373_);
v_a_4484_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4486_ = v___x_4415_;
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_dec(v___x_4415_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4489_; 
if (v_isShared_4487_ == 0)
{
v___x_4489_ = v___x_4486_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4484_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
v___jp_4388_:
{
if (lean_obj_tag(v___y_4389_) == 0)
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4402_; 
v_a_4390_ = lean_ctor_get(v___y_4389_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___y_4389_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4392_ = v___y_4389_;
v_isShared_4393_ = v_isSharedCheck_4402_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___y_4389_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4402_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
if (lean_obj_tag(v_a_4390_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4396_; 
lean_dec(v_a_4374_);
lean_dec_ref(v_config_4373_);
v_a_4394_ = lean_ctor_get(v_a_4390_, 0);
lean_inc(v_a_4394_);
lean_dec_ref_known(v_a_4390_, 1);
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 0, v_a_4394_);
v___x_4396_ = v___x_4392_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4394_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
lean_del_object(v___x_4392_);
v_a_4398_ = lean_ctor_get(v_a_4390_, 0);
lean_inc(v_a_4398_);
lean_dec_ref_known(v_a_4390_, 1);
v___x_4399_ = lean_unsigned_to_nat(1u);
v___x_4400_ = lean_nat_add(v_a_4374_, v___x_4399_);
lean_dec(v_a_4374_);
v_a_4374_ = v___x_4400_;
v_b_4375_ = v_a_4398_;
goto _start;
}
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v_a_4374_);
lean_dec_ref(v_config_4373_);
v_a_4403_ = lean_ctor_get(v___y_4389_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___y_4389_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___y_4389_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___y_4389_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_4492_ = _args[0];
lean_object* v___x_4493_ = _args[1];
lean_object* v_config_4494_ = _args[2];
lean_object* v_a_4495_ = _args[3];
lean_object* v_b_4496_ = _args[4];
lean_object* v___y_4497_ = _args[5];
lean_object* v___y_4498_ = _args[6];
lean_object* v___y_4499_ = _args[7];
lean_object* v___y_4500_ = _args[8];
lean_object* v___y_4501_ = _args[9];
lean_object* v___y_4502_ = _args[10];
lean_object* v___y_4503_ = _args[11];
lean_object* v___y_4504_ = _args[12];
lean_object* v___y_4505_ = _args[13];
lean_object* v___y_4506_ = _args[14];
lean_object* v___y_4507_ = _args[15];
lean_object* v___y_4508_ = _args[16];
_start:
{
lean_object* v_res_4509_; 
v_res_4509_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_upperBound_4492_, v___x_4493_, v_config_4494_, v_a_4495_, v_b_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec_ref(v___x_4493_);
lean_dec(v_upperBound_4492_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object* v_config_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v___x_4523_; lean_object* v_hypotheses_4524_; lean_object* v___x_4525_; lean_object* v_newHyps_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4523_ = lean_st_ref_get(v___y_4512_);
v_hypotheses_4524_ = lean_ctor_get(v___x_4523_, 5);
lean_inc_ref(v_hypotheses_4524_);
lean_dec(v___x_4523_);
v___x_4525_ = lean_array_get_size(v_hypotheses_4524_);
v_newHyps_4526_ = lean_mk_empty_array_with_capacity(v___x_4525_);
v___x_4527_ = lean_unsigned_to_nat(0u);
v___x_4528_ = lean_box(0);
v___x_4529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4529_, 0, v___x_4528_);
lean_ctor_set(v___x_4529_, 1, v_newHyps_4526_);
v___x_4530_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v___x_4525_, v_hypotheses_4524_, v_config_4510_, v___x_4527_, v___x_4529_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
lean_dec_ref(v_hypotheses_4524_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4562_; 
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4533_ = v___x_4530_;
v_isShared_4534_ = v_isSharedCheck_4562_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4530_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4562_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v_fst_4535_; 
v_fst_4535_ = lean_ctor_get(v_a_4531_, 0);
if (lean_obj_tag(v_fst_4535_) == 0)
{
lean_object* v_snd_4536_; lean_object* v___x_4537_; lean_object* v_rewriteSimpCache_4538_; lean_object* v_rewriteDSimpCache_4539_; lean_object* v_acCache_4540_; lean_object* v_typeAnalysis_4541_; lean_object* v_target_4542_; uint8_t v_didChange_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4556_; 
v_snd_4536_ = lean_ctor_get(v_a_4531_, 1);
lean_inc(v_snd_4536_);
lean_dec(v_a_4531_);
v___x_4537_ = lean_st_ref_take(v___y_4512_);
v_rewriteSimpCache_4538_ = lean_ctor_get(v___x_4537_, 0);
v_rewriteDSimpCache_4539_ = lean_ctor_get(v___x_4537_, 1);
v_acCache_4540_ = lean_ctor_get(v___x_4537_, 2);
v_typeAnalysis_4541_ = lean_ctor_get(v___x_4537_, 3);
v_target_4542_ = lean_ctor_get(v___x_4537_, 4);
v_didChange_4543_ = lean_ctor_get_uint8(v___x_4537_, sizeof(void*)*6);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4556_ == 0)
{
lean_object* v_unused_4557_; 
v_unused_4557_ = lean_ctor_get(v___x_4537_, 5);
lean_dec(v_unused_4557_);
v___x_4545_ = v___x_4537_;
v_isShared_4546_ = v_isSharedCheck_4556_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_target_4542_);
lean_inc(v_typeAnalysis_4541_);
lean_inc(v_acCache_4540_);
lean_inc(v_rewriteDSimpCache_4539_);
lean_inc(v_rewriteSimpCache_4538_);
lean_dec(v___x_4537_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4556_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 5, v_snd_4536_);
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_rewriteSimpCache_4538_);
lean_ctor_set(v_reuseFailAlloc_4555_, 1, v_rewriteDSimpCache_4539_);
lean_ctor_set(v_reuseFailAlloc_4555_, 2, v_acCache_4540_);
lean_ctor_set(v_reuseFailAlloc_4555_, 3, v_typeAnalysis_4541_);
lean_ctor_set(v_reuseFailAlloc_4555_, 4, v_target_4542_);
lean_ctor_set(v_reuseFailAlloc_4555_, 5, v_snd_4536_);
lean_ctor_set_uint8(v_reuseFailAlloc_4555_, sizeof(void*)*6, v_didChange_4543_);
v___x_4548_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
lean_object* v___x_4549_; uint8_t v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4553_; 
v___x_4549_ = lean_st_ref_set(v___y_4512_, v___x_4548_);
v___x_4550_ = 0;
v___x_4551_ = lean_box(v___x_4550_);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 0, v___x_4551_);
v___x_4553_ = v___x_4533_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4551_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
}
else
{
lean_object* v_val_4558_; lean_object* v___x_4560_; 
lean_inc_ref(v_fst_4535_);
lean_dec(v_a_4531_);
v_val_4558_ = lean_ctor_get(v_fst_4535_, 0);
lean_inc(v_val_4558_);
lean_dec_ref_known(v_fst_4535_, 1);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 0, v_val_4558_);
v___x_4560_ = v___x_4533_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_val_4558_);
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
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
v_a_4563_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4530_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4530_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v_config_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
lean_object* v_res_4584_; 
v_res_4584_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(v_config_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v_config_4597_; lean_object* v___x_4598_; lean_object* v_maxSteps_4599_; lean_object* v_target_4600_; lean_object* v___x_4601_; lean_object* v_config_4602_; lean_object* v___f_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v_config_4597_ = lean_ctor_get(v___y_4585_, 0);
v___x_4598_ = lean_st_ref_get(v___y_4586_);
v_maxSteps_4599_ = lean_ctor_get(v_config_4597_, 1);
v_target_4600_ = lean_ctor_get(v___x_4598_, 4);
lean_inc_ref(v_target_4600_);
lean_dec(v___x_4598_);
v___x_4601_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_4599_);
v_config_4602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_4602_, 0, v_maxSteps_4599_);
lean_ctor_set(v_config_4602_, 1, v___x_4601_);
v___f_4603_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_4603_, 0, v_config_4602_);
v___x_4604_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_4600_);
lean_dec_ref(v_target_4600_);
v___x_4605_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__3___redArg(v___x_4604_, v___f_4603_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
return v___x_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object* v_cls_4627_, lean_object* v_msg_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_){
_start:
{
lean_object* v___x_4641_; 
v___x_4641_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_4627_, v_msg_4628_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_cls_4642_, lean_object* v_msg_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(v_cls_4642_, v_msg_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
lean_dec(v___y_4646_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object* v_mvarId_4657_, lean_object* v_val_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
lean_object* v___x_4671_; 
v___x_4671_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_mvarId_4657_, v_val_4658_, v___y_4667_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___boxed(lean_object* v_mvarId_4672_, lean_object* v_val_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(v_mvarId_4672_, v_val_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object* v_upperBound_4687_, lean_object* v___x_4688_, lean_object* v_config_4689_, lean_object* v_inst_4690_, lean_object* v_R_4691_, lean_object* v_a_4692_, lean_object* v_b_4693_, lean_object* v_c_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
lean_object* v___x_4707_; 
v___x_4707_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_upperBound_4687_, v___x_4688_, v_config_4689_, v_a_4692_, v_b_4693_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_4708_ = _args[0];
lean_object* v___x_4709_ = _args[1];
lean_object* v_config_4710_ = _args[2];
lean_object* v_inst_4711_ = _args[3];
lean_object* v_R_4712_ = _args[4];
lean_object* v_a_4713_ = _args[5];
lean_object* v_b_4714_ = _args[6];
lean_object* v_c_4715_ = _args[7];
lean_object* v___y_4716_ = _args[8];
lean_object* v___y_4717_ = _args[9];
lean_object* v___y_4718_ = _args[10];
lean_object* v___y_4719_ = _args[11];
lean_object* v___y_4720_ = _args[12];
lean_object* v___y_4721_ = _args[13];
lean_object* v___y_4722_ = _args[14];
lean_object* v___y_4723_ = _args[15];
lean_object* v___y_4724_ = _args[16];
lean_object* v___y_4725_ = _args[17];
lean_object* v___y_4726_ = _args[18];
lean_object* v___y_4727_ = _args[19];
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(v_upperBound_4708_, v___x_4709_, v_config_4710_, v_inst_4711_, v_R_4712_, v_a_4713_, v_b_4714_, v_c_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec_ref(v___x_4709_);
lean_dec(v_upperBound_4708_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1(lean_object* v_00_u03b2_4729_, lean_object* v_x_4730_, lean_object* v_x_4731_, lean_object* v_x_4732_){
_start:
{
lean_object* v___x_4733_; 
v___x_4733_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1___redArg(v_x_4730_, v_x_4731_, v_x_4732_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_4734_, lean_object* v_x_4735_, size_t v_x_4736_, size_t v_x_4737_, lean_object* v_x_4738_, lean_object* v_x_4739_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___redArg(v_x_4735_, v_x_4736_, v_x_4737_, v_x_4738_, v_x_4739_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_4741_, lean_object* v_x_4742_, lean_object* v_x_4743_, lean_object* v_x_4744_, lean_object* v_x_4745_, lean_object* v_x_4746_){
_start:
{
size_t v_x_35024__boxed_4747_; size_t v_x_35025__boxed_4748_; lean_object* v_res_4749_; 
v_x_35024__boxed_4747_ = lean_unbox_usize(v_x_4743_);
lean_dec(v_x_4743_);
v_x_35025__boxed_4748_ = lean_unbox_usize(v_x_4744_);
lean_dec(v_x_4744_);
v_res_4749_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3(v_00_u03b2_4741_, v_x_4742_, v_x_35024__boxed_4747_, v_x_35025__boxed_4748_, v_x_4745_, v_x_4746_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_4750_, lean_object* v_n_4751_, lean_object* v_k_4752_, lean_object* v_v_4753_){
_start:
{
lean_object* v___x_4754_; 
v___x_4754_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__5___redArg(v_n_4751_, v_k_4752_, v_v_4753_);
return v___x_4754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_4755_, size_t v_depth_4756_, lean_object* v_keys_4757_, lean_object* v_vals_4758_, lean_object* v_heq_4759_, lean_object* v_i_4760_, lean_object* v_entries_4761_){
_start:
{
lean_object* v___x_4762_; 
v___x_4762_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__6___redArg(v_depth_4756_, v_keys_4757_, v_vals_4758_, v_i_4760_, v_entries_4761_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_4763_, lean_object* v_depth_4764_, lean_object* v_keys_4765_, lean_object* v_vals_4766_, lean_object* v_heq_4767_, lean_object* v_i_4768_, lean_object* v_entries_4769_){
_start:
{
size_t v_depth_boxed_4770_; lean_object* v_res_4771_; 
v_depth_boxed_4770_ = lean_unbox_usize(v_depth_4764_);
lean_dec(v_depth_4764_);
v_res_4771_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__6(v_00_u03b2_4763_, v_depth_boxed_4770_, v_keys_4765_, v_vals_4766_, v_heq_4767_, v_i_4768_, v_entries_4769_);
lean_dec_ref(v_vals_4766_);
lean_dec_ref(v_keys_4765_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_4772_, lean_object* v_x_4773_, lean_object* v_x_4774_, lean_object* v_x_4775_, lean_object* v_x_4776_){
_start:
{
lean_object* v___x_4777_; 
v___x_4777_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(v_x_4773_, v_x_4774_, v_x_4775_, v_x_4776_);
return v___x_4777_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_AC_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_AC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
