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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_merge___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
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
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Operations mismatch:\n      the left-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n        "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\n      but the right-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Canonicalizing with respect to operation: '"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to recognize operation: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___boxed(lean_object**);
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
uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = lean_expr_eqv(v_x_46_, v_x_47_);
return v___x_48_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_46_ = stack[0].m_obj;
lean_object* v_x_47_ = stack[1].m_obj;
uint8_t v_res_49_;
v_res_49_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq(v_x_46_, v_x_47_);
stack->m_num = v_res_49_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq___boxed(lean_object* v_x_50_, lean_object* v_x_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instBEqOp_beq(v_x_50_, v_x_51_);
lean_dec_ref(v_x_51_);
lean_dec_ref(v_x_50_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(2u);
v___x_63_ = lean_nat_to_int(v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_to_int(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr(lean_object* v_x_66_, lean_object* v_prec_67_){
_start:
{
lean_object* v___y_69_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1024u);
v___x_79_ = lean_nat_dec_le(v___x_78_, v_prec_67_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__3);
v___y_69_ = v___x_80_;
goto v___jp_68_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__4);
v___y_69_ = v___x_81_;
goto v___jp_68_;
}
v___jp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_70_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___closed__2));
v___x_71_ = lean_unsigned_to_nat(1024u);
v___x_72_ = l_Lean_instReprExpr_repr(v_x_66_, v___x_71_);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_70_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
lean_inc(v___y_69_);
v___x_74_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_74_, 0, v___y_69_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = 0;
v___x_76_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_75_);
v___x_77_ = l_Repr_addAppParen(v___x_76_, v_prec_67_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr___boxed(lean_object* v_x_82_, lean_object* v_prec_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_Tactic_BVDecide_Normalize_instReprOp_repr(v_x_82_, v_prec_83_);
lean_dec(v_prec_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(lean_object* v_e_92_){
_start:
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = l_Lean_Expr_cleanupAnnotations(v_e_92_);
v___x_94_ = l_Lean_Expr_isApp(v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
lean_dec_ref(v___x_93_);
v___x_95_ = lean_box(0);
return v___x_95_;
}
else
{
lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_96_ = l_Lean_Expr_appFnCleanup___redArg(v___x_93_);
v___x_97_ = l_Lean_Expr_isApp(v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
lean_dec_ref(v___x_96_);
v___x_98_ = lean_box(0);
return v___x_98_;
}
else
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = l_Lean_Expr_appFnCleanup___redArg(v___x_96_);
v___x_100_ = l_Lean_Expr_isApp(v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
lean_dec_ref(v___x_99_);
v___x_101_ = lean_box(0);
return v___x_101_;
}
else
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_99_);
v___x_103_ = l_Lean_Expr_isApp(v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
lean_dec_ref(v___x_102_);
v___x_104_ = lean_box(0);
return v___x_104_;
}
else
{
lean_object* v_arg_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_arg_105_ = lean_ctor_get(v___x_102_, 1);
lean_inc_ref(v_arg_105_);
v___x_106_ = l_Lean_Expr_appFnCleanup___redArg(v___x_102_);
v___x_107_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2));
v___x_108_ = l_Lean_Expr_isConstOf(v___x_106_, v___x_107_);
lean_dec_ref(v___x_106_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
lean_dec_ref(v_arg_105_);
v___x_109_ = lean_box(0);
return v___x_109_;
}
else
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = l_Lean_Expr_cleanupAnnotations(v_arg_105_);
v___x_111_ = l_Lean_Expr_isApp(v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
lean_dec_ref(v___x_110_);
v___x_112_ = lean_box(0);
return v___x_112_;
}
else
{
lean_object* v_arg_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_arg_113_ = lean_ctor_get(v___x_110_, 1);
lean_inc_ref(v_arg_113_);
v___x_114_ = l_Lean_Expr_appFnCleanup___redArg(v___x_110_);
v___x_115_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__1));
v___x_116_ = l_Lean_Expr_isConstOf(v___x_114_, v___x_115_);
lean_dec_ref(v___x_114_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
lean_dec_ref(v_arg_113_);
v___x_117_ = lean_box(0);
return v___x_117_;
}
else
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_118_, 0, v_arg_113_);
return v___x_118_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(lean_object* v_x_119_){
_start:
{
if (lean_obj_tag(v_x_119_) == 5)
{
lean_object* v_fn_120_; 
v_fn_120_ = lean_ctor_get(v_x_119_, 0);
lean_inc_ref(v_fn_120_);
lean_dec_ref_known(v_x_119_, 2);
if (lean_obj_tag(v_fn_120_) == 5)
{
lean_object* v_fn_121_; lean_object* v___x_122_; 
v_fn_121_ = lean_ctor_get(v_fn_120_, 0);
lean_inc_ref(v_fn_121_);
lean_dec_ref_known(v_fn_120_, 2);
v___x_122_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(v_fn_121_);
return v___x_122_;
}
else
{
lean_object* v___x_123_; 
lean_dec_ref(v_fn_120_);
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
else
{
lean_object* v___x_124_; 
lean_dec_ref(v_x_119_);
v___x_124_ = lean_box(0);
return v___x_124_;
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = l_Lean_Level_ofNat(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_box(0);
v___x_128_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0);
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1);
v___x_131_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0);
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2);
v___x_134_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0);
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3);
v___x_137_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2));
v___x_138_ = l_Lean_mkConst(v___x_137_, v___x_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(lean_object* v_x_139_){
_start:
{
lean_object* v_bv_140_; lean_object* v_inst_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
lean_inc_ref(v_x_139_);
v_bv_140_ = l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType(v_x_139_);
v_inst_141_ = l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul(v_x_139_);
v___x_142_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4);
lean_inc_ref_n(v_bv_140_, 2);
v___x_143_ = l_Lean_mkApp4(v___x_142_, v_bv_140_, v_bv_140_, v_bv_140_, v_inst_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(lean_object* v_x_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(1u);
v___x_146_ = l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit(v_x_144_, v___x_145_);
return v___x_146_;
}
}
uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(lean_object* v_op_x27_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(v_op_x27_147_);
if (lean_obj_tag(v___x_148_) == 1)
{
uint8_t v___x_149_; 
lean_dec_ref_known(v___x_148_, 1);
v___x_149_ = 1;
return v___x_149_;
}
else
{
uint8_t v___x_150_; 
lean_dec(v___x_148_);
v___x_150_ = 0;
return v___x_150_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_x27_147_ = stack[0].m_obj;
uint8_t v_res_151_;
v_res_151_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_op_x27_147_);
stack->m_num = v_res_151_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg___boxed(lean_object* v_op_x27_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_op_x27_152_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind(lean_object* v_op_155_, lean_object* v_op_x27_156_){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_op_x27_156_);
return v___x_157_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_155_ = stack[0].m_obj;
lean_object* v_op_x27_156_ = stack[1].m_obj;
uint8_t v_res_158_;
v_res_158_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind(v_op_155_, v_op_x27_156_);
stack->m_num = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___boxed(lean_object* v_op_159_, lean_object* v_op_x27_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind(v_op_159_, v_op_x27_160_);
lean_dec_ref(v_op_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___lam__0(lean_object* v_op_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_163_);
v___x_165_ = l_Lean_MessageData_ofExpr(v___x_164_);
return v___x_165_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(lean_object* v_x_168_, lean_object* v_s_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; 
lean_inc(v_a_175_);
lean_inc_ref(v_a_174_);
lean_inc(v_a_173_);
lean_inc_ref(v_a_172_);
lean_inc(v_a_171_);
lean_inc_ref(v_a_170_);
v___x_177_ = lean_apply_8(v_x_168_, v_s_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, lean_box(0));
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_186_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_186_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_186_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_186_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_fst_182_; lean_object* v___x_184_; 
v_fst_182_ = lean_ctor_get(v_a_178_, 0);
lean_inc(v_fst_182_);
lean_dec(v_a_178_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v_fst_182_);
v___x_184_ = v___x_180_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_fst_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_a_187_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_177_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_177_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_168_ = stack[0].m_obj;
lean_object* v_s_169_ = stack[1].m_obj;
lean_object* v_a_170_ = stack[2].m_obj;
lean_object* v_a_171_ = stack[3].m_obj;
lean_object* v_a_172_ = stack[4].m_obj;
lean_object* v_a_173_ = stack[5].m_obj;
lean_object* v_a_174_ = stack[6].m_obj;
lean_object* v_a_175_ = stack[7].m_obj;
lean_object* v_res_195_;
v_res_195_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v_x_168_, v_s_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg___boxed(lean_object* v_x_196_, lean_object* v_s_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v_x_196_, v_s_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
return v_res_205_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(lean_object* v_00_u03b1_206_, lean_object* v_x_207_, lean_object* v_s_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v_x_207_, v_s_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
return v___x_216_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_207_ = stack[1].m_obj;
lean_object* v_s_208_ = stack[2].m_obj;
lean_object* v_a_209_ = stack[3].m_obj;
lean_object* v_a_210_ = stack[4].m_obj;
lean_object* v_a_211_ = stack[5].m_obj;
lean_object* v_a_212_ = stack[6].m_obj;
lean_object* v_a_213_ = stack[7].m_obj;
lean_object* v_a_214_ = stack[8].m_obj;
lean_object* v_res_217_;
v_res_217_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(lean_box(0), v_x_207_, v_s_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___boxed(lean_object* v_00_u03b1_218_, lean_object* v_x_219_, lean_object* v_s_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(v_00_u03b1_218_, v_x_219_, v_s_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(lean_object* v_a_229_, lean_object* v_b_230_, lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
lean_dec(v_b_230_);
lean_dec_ref(v_a_229_);
return v_x_231_;
}
else
{
lean_object* v_key_232_; lean_object* v_value_233_; lean_object* v_tail_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_246_; 
v_key_232_ = lean_ctor_get(v_x_231_, 0);
v_value_233_ = lean_ctor_get(v_x_231_, 1);
v_tail_234_ = lean_ctor_get(v_x_231_, 2);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_246_ == 0)
{
v___x_236_ = v_x_231_;
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_tail_234_);
lean_inc(v_value_233_);
lean_inc(v_key_232_);
lean_dec(v_x_231_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
uint8_t v___x_238_; 
v___x_238_ = lean_expr_eqv(v_key_232_, v_a_229_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_229_, v_b_230_, v_tail_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 2, v___x_239_);
v___x_241_ = v___x_236_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_key_232_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_value_233_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
else
{
lean_object* v___x_244_; 
lean_dec(v_value_233_);
lean_dec(v_key_232_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v_b_230_);
lean_ctor_set(v___x_236_, 0, v_a_229_);
v___x_244_ = v___x_236_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_229_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_b_230_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_tail_234_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object* v_a_247_, lean_object* v_x_248_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
uint8_t v___x_249_; 
v___x_249_ = 0;
return v___x_249_;
}
else
{
lean_object* v_key_250_; lean_object* v_tail_251_; uint8_t v___x_252_; 
v_key_250_ = lean_ctor_get(v_x_248_, 0);
v_tail_251_ = lean_ctor_get(v_x_248_, 2);
v___x_252_ = lean_expr_eqv(v_key_250_, v_a_247_);
if (v___x_252_ == 0)
{
v_x_248_ = v_tail_251_;
goto _start;
}
else
{
return v___x_252_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_247_ = stack[0].m_obj;
lean_object* v_x_248_ = stack[1].m_obj;
uint8_t v_res_254_;
v_res_254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_247_, v_x_248_);
stack->m_num = v_res_254_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object* v_a_255_, lean_object* v_x_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_255_, v_x_256_);
lean_dec(v_x_256_);
lean_dec_ref(v_a_255_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
return v_x_259_;
}
else
{
lean_object* v_key_261_; lean_object* v_value_262_; lean_object* v_tail_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_286_; 
v_key_261_ = lean_ctor_get(v_x_260_, 0);
v_value_262_ = lean_ctor_get(v_x_260_, 1);
v_tail_263_ = lean_ctor_get(v_x_260_, 2);
v_isSharedCheck_286_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_286_ == 0)
{
v___x_265_ = v_x_260_;
v_isShared_266_ = v_isSharedCheck_286_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_tail_263_);
lean_inc(v_value_262_);
lean_inc(v_key_261_);
lean_dec(v_x_260_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_286_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; uint64_t v___x_268_; uint64_t v___x_269_; uint64_t v___x_270_; uint64_t v_fold_271_; uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_267_ = lean_array_get_size(v_x_259_);
v___x_268_ = l_Lean_Expr_hash(v_key_261_);
v___x_269_ = 32ULL;
v___x_270_ = lean_uint64_shift_right(v___x_268_, v___x_269_);
v_fold_271_ = lean_uint64_xor(v___x_268_, v___x_270_);
v___x_272_ = 16ULL;
v___x_273_ = lean_uint64_shift_right(v_fold_271_, v___x_272_);
v___x_274_ = lean_uint64_xor(v_fold_271_, v___x_273_);
v___x_275_ = lean_uint64_to_usize(v___x_274_);
v___x_276_ = lean_usize_of_nat(v___x_267_);
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_sub(v___x_276_, v___x_277_);
v___x_279_ = lean_usize_land(v___x_275_, v___x_278_);
v___x_280_ = lean_array_uget_borrowed(v_x_259_, v___x_279_);
lean_inc(v___x_280_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 2, v___x_280_);
v___x_282_ = v___x_265_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_key_261_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_value_262_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v___x_280_);
v___x_282_ = v_reuseFailAlloc_285_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; 
v___x_283_ = lean_array_uset(v_x_259_, v___x_279_, v___x_282_);
v_x_259_ = v___x_283_;
v_x_260_ = v_tail_263_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(lean_object* v_i_287_, lean_object* v_source_288_, lean_object* v_target_289_){
_start:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_array_get_size(v_source_288_);
v___x_291_ = lean_nat_dec_lt(v_i_287_, v___x_290_);
if (v___x_291_ == 0)
{
lean_dec_ref(v_source_288_);
lean_dec(v_i_287_);
return v_target_289_;
}
else
{
lean_object* v_es_292_; lean_object* v___x_293_; lean_object* v_source_294_; lean_object* v_target_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_es_292_ = lean_array_fget(v_source_288_, v_i_287_);
v___x_293_ = lean_box(0);
v_source_294_ = lean_array_fset(v_source_288_, v_i_287_, v___x_293_);
v_target_295_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_289_, v_es_292_);
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_add(v_i_287_, v___x_296_);
lean_dec(v_i_287_);
v_i_287_ = v___x_297_;
v_source_288_ = v_source_294_;
v_target_289_ = v_target_295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(lean_object* v_data_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_nbuckets_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_300_ = lean_array_get_size(v_data_299_);
v___x_301_ = lean_unsigned_to_nat(2u);
v_nbuckets_302_ = lean_nat_mul(v___x_300_, v___x_301_);
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_box(0);
v___x_305_ = lean_mk_array(v_nbuckets_302_, v___x_304_);
v___x_306_ = lean_array_propagate_mark(v_data_299_, v___x_305_);
v___x_307_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v___x_303_, v_data_299_, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object* v_m_308_, lean_object* v_a_309_, lean_object* v_b_310_){
_start:
{
lean_object* v_size_311_; lean_object* v_buckets_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_355_; 
v_size_311_ = lean_ctor_get(v_m_308_, 0);
v_buckets_312_ = lean_ctor_get(v_m_308_, 1);
v_isSharedCheck_355_ = !lean_is_exclusive(v_m_308_);
if (v_isSharedCheck_355_ == 0)
{
v___x_314_ = v_m_308_;
v_isShared_315_ = v_isSharedCheck_355_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_buckets_312_);
lean_inc(v_size_311_);
lean_dec(v_m_308_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_355_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; uint64_t v___x_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v_fold_320_; uint64_t v___x_321_; uint64_t v___x_322_; uint64_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; size_t v___x_327_; size_t v___x_328_; lean_object* v_bkt_329_; uint8_t v___x_330_; 
v___x_316_ = lean_array_get_size(v_buckets_312_);
v___x_317_ = l_Lean_Expr_hash(v_a_309_);
v___x_318_ = 32ULL;
v___x_319_ = lean_uint64_shift_right(v___x_317_, v___x_318_);
v_fold_320_ = lean_uint64_xor(v___x_317_, v___x_319_);
v___x_321_ = 16ULL;
v___x_322_ = lean_uint64_shift_right(v_fold_320_, v___x_321_);
v___x_323_ = lean_uint64_xor(v_fold_320_, v___x_322_);
v___x_324_ = lean_uint64_to_usize(v___x_323_);
v___x_325_ = lean_usize_of_nat(v___x_316_);
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_sub(v___x_325_, v___x_326_);
v___x_328_ = lean_usize_land(v___x_324_, v___x_327_);
v_bkt_329_ = lean_array_uget_borrowed(v_buckets_312_, v___x_328_);
v___x_330_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_309_, v_bkt_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v_size_x27_332_; lean_object* v___x_333_; lean_object* v_buckets_x27_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v_size_x27_332_ = lean_nat_add(v_size_311_, v___x_331_);
lean_dec(v_size_311_);
lean_inc(v_bkt_329_);
v___x_333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_333_, 0, v_a_309_);
lean_ctor_set(v___x_333_, 1, v_b_310_);
lean_ctor_set(v___x_333_, 2, v_bkt_329_);
v_buckets_x27_334_ = lean_array_uset(v_buckets_312_, v___x_328_, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(4u);
v___x_336_ = lean_nat_mul(v_size_x27_332_, v___x_335_);
v___x_337_ = lean_unsigned_to_nat(3u);
v___x_338_ = lean_nat_div(v___x_336_, v___x_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_array_get_size(v_buckets_x27_334_);
v___x_340_ = lean_nat_dec_le(v___x_338_, v___x_339_);
lean_dec(v___x_338_);
if (v___x_340_ == 0)
{
lean_object* v_val_341_; lean_object* v___x_343_; 
v_val_341_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_buckets_x27_334_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v_val_341_);
lean_ctor_set(v___x_314_, 0, v_size_x27_332_);
v___x_343_ = v___x_314_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_size_x27_332_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_val_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
lean_object* v___x_346_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v_buckets_x27_334_);
lean_ctor_set(v___x_314_, 0, v_size_x27_332_);
v___x_346_ = v___x_314_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_size_x27_332_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_buckets_x27_334_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v___x_348_; lean_object* v_buckets_x27_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
lean_inc(v_bkt_329_);
v___x_348_ = lean_box(0);
v_buckets_x27_349_ = lean_array_uset(v_buckets_312_, v___x_328_, v___x_348_);
v___x_350_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_309_, v_b_310_, v_bkt_329_);
v___x_351_ = lean_array_uset(v_buckets_x27_349_, v___x_328_, v___x_350_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v___x_351_);
v___x_353_ = v___x_314_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_size_311_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object* v_a_356_, lean_object* v_x_357_){
_start:
{
if (lean_obj_tag(v_x_357_) == 0)
{
lean_object* v___x_358_; 
v___x_358_ = lean_box(0);
return v___x_358_;
}
else
{
lean_object* v_key_359_; lean_object* v_value_360_; lean_object* v_tail_361_; uint8_t v___x_362_; 
v_key_359_ = lean_ctor_get(v_x_357_, 0);
v_value_360_ = lean_ctor_get(v_x_357_, 1);
v_tail_361_ = lean_ctor_get(v_x_357_, 2);
v___x_362_ = lean_expr_eqv(v_key_359_, v_a_356_);
if (v___x_362_ == 0)
{
v_x_357_ = v_tail_361_;
goto _start;
}
else
{
lean_object* v___x_364_; 
lean_inc(v_value_360_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v_value_360_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_365_, lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_365_, v_x_366_);
lean_dec(v_x_366_);
lean_dec_ref(v_a_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object* v_m_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_buckets_370_; lean_object* v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v___x_374_; uint64_t v_fold_375_; uint64_t v___x_376_; uint64_t v___x_377_; uint64_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_buckets_370_ = lean_ctor_get(v_m_368_, 1);
v___x_371_ = lean_array_get_size(v_buckets_370_);
v___x_372_ = l_Lean_Expr_hash(v_a_369_);
v___x_373_ = 32ULL;
v___x_374_ = lean_uint64_shift_right(v___x_372_, v___x_373_);
v_fold_375_ = lean_uint64_xor(v___x_372_, v___x_374_);
v___x_376_ = 16ULL;
v___x_377_ = lean_uint64_shift_right(v_fold_375_, v___x_376_);
v___x_378_ = lean_uint64_xor(v_fold_375_, v___x_377_);
v___x_379_ = lean_uint64_to_usize(v___x_378_);
v___x_380_ = lean_usize_of_nat(v___x_371_);
v___x_381_ = ((size_t)1ULL);
v___x_382_ = lean_usize_sub(v___x_380_, v___x_381_);
v___x_383_ = lean_usize_land(v___x_379_, v___x_382_);
v___x_384_ = lean_array_uget_borrowed(v_buckets_370_, v___x_383_);
v___x_385_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_369_, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object* v_m_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_386_, v_a_387_);
lean_dec_ref(v_a_387_);
lean_dec_ref(v_m_386_);
return v_res_388_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(lean_object* v_e_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_op_392_; lean_object* v_exprToVarIndex_393_; lean_object* v_varToExpr_394_; lean_object* v___x_395_; 
v_op_392_ = lean_ctor_get(v_a_390_, 0);
v_exprToVarIndex_393_ = lean_ctor_get(v_a_390_, 1);
v_varToExpr_394_ = lean_ctor_get(v_a_390_, 2);
v___x_395_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_exprToVarIndex_393_, v_e_389_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_407_; 
lean_inc_ref(v_varToExpr_394_);
lean_inc_ref(v_exprToVarIndex_393_);
lean_inc_ref(v_op_392_);
v_isSharedCheck_407_ = !lean_is_exclusive(v_a_390_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; lean_object* v_unused_409_; lean_object* v_unused_410_; 
v_unused_408_ = lean_ctor_get(v_a_390_, 2);
lean_dec(v_unused_408_);
v_unused_409_ = lean_ctor_get(v_a_390_, 1);
lean_dec(v_unused_409_);
v_unused_410_ = lean_ctor_get(v_a_390_, 0);
lean_dec(v_unused_410_);
v___x_397_ = v_a_390_;
v_isShared_398_ = v_isSharedCheck_407_;
goto v_resetjp_396_;
}
else
{
lean_dec(v_a_390_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_407_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_size_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v_size_399_ = lean_ctor_get(v_exprToVarIndex_393_, 0);
lean_inc_n(v_size_399_, 2);
lean_inc_ref(v_e_389_);
v___x_400_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_exprToVarIndex_393_, v_e_389_, v_size_399_);
v___x_401_ = lean_array_push(v_varToExpr_394_, v_e_389_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 2, v___x_401_);
lean_ctor_set(v___x_397_, 1, v___x_400_);
v___x_403_ = v___x_397_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_op_392_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v___x_401_);
v___x_403_ = v_reuseFailAlloc_406_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v_size_399_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
}
else
{
lean_object* v_val_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_419_; 
lean_dec_ref(v_e_389_);
v_val_411_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_419_ == 0)
{
v___x_413_ = v___x_395_;
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_val_411_);
lean_dec(v___x_395_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v_val_411_);
lean_ctor_set(v___x_415_, 1, v_a_390_);
if (v_isShared_414_ == 0)
{
lean_ctor_set_tag(v___x_413_, 0);
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_389_ = stack[0].m_obj;
lean_object* v_a_390_ = stack[1].m_obj;
lean_object* v_res_420_;
v_res_420_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_389_, v_a_390_);
stack->m_obj
 = v_res_420_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object* v_e_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_421_, v_a_422_);
return v_res_424_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(lean_object* v_e_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_425_, v_a_426_);
return v___x_434_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_425_ = stack[0].m_obj;
lean_object* v_a_426_ = stack[1].m_obj;
lean_object* v_a_427_ = stack[2].m_obj;
lean_object* v_a_428_ = stack[3].m_obj;
lean_object* v_a_429_ = stack[4].m_obj;
lean_object* v_a_430_ = stack[5].m_obj;
lean_object* v_a_431_ = stack[6].m_obj;
lean_object* v_a_432_ = stack[7].m_obj;
lean_object* v_res_435_;
v_res_435_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(v_e_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
stack->m_obj
 = v_res_435_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___boxed(lean_object* v_e_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(v_e_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(lean_object* v_00_u03b2_446_, lean_object* v_m_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_447_, v_a_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object* v_00_u03b2_450_, lean_object* v_m_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(v_00_u03b2_450_, v_m_451_, v_a_452_);
lean_dec_ref(v_a_452_);
lean_dec_ref(v_m_451_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1(lean_object* v_00_u03b2_454_, lean_object* v_m_455_, lean_object* v_a_456_, lean_object* v_b_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_m_455_, v_a_456_, v_b_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object* v_00_u03b2_459_, lean_object* v_a_460_, lean_object* v_x_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_460_, v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_463_, lean_object* v_a_464_, lean_object* v_x_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(v_00_u03b2_463_, v_a_464_, v_x_465_);
lean_dec(v_x_465_);
lean_dec_ref(v_a_464_);
return v_res_466_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object* v_00_u03b2_467_, lean_object* v_a_468_, lean_object* v_x_469_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_468_, v_x_469_);
return v___x_470_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_468_ = stack[1].m_obj;
lean_object* v_x_469_ = stack[2].m_obj;
uint8_t v_res_471_;
v_res_471_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_box(0), v_a_468_, v_x_469_);
stack->m_num = v_res_471_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_472_, lean_object* v_a_473_, lean_object* v_x_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(v_00_u03b2_472_, v_a_473_, v_x_474_);
lean_dec(v_x_474_);
lean_dec_ref(v_a_473_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3(lean_object* v_00_u03b2_477_, lean_object* v_data_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_data_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4(lean_object* v_00_u03b2_480_, lean_object* v_a_481_, lean_object* v_b_482_, lean_object* v_x_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_481_, v_b_482_, v_x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_485_, lean_object* v_i_486_, lean_object* v_source_487_, lean_object* v_target_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v_i_486_, v_source_487_, v_target_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_491_, v_x_492_);
return v___x_493_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object* v_msgData_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; lean_object* v_env_501_; uint8_t v___x_502_; lean_object* v_env_503_; lean_object* v___x_504_; lean_object* v_toCold_505_; lean_object* v_mctx_506_; lean_object* v_lctx_507_; lean_object* v_options_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_500_ = lean_st_ref_get(v___y_498_);
v_env_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc_ref(v_env_501_);
lean_dec(v___x_500_);
v___x_502_ = 0;
v_env_503_ = l_Lean_Environment_setRecordingDeps(v_env_501_, v___x_502_);
v___x_504_ = lean_st_ref_get(v___y_496_);
v_toCold_505_ = lean_ctor_get(v___y_497_, 0);
v_mctx_506_ = lean_ctor_get(v___x_504_, 0);
lean_inc_ref(v_mctx_506_);
lean_dec(v___x_504_);
v_lctx_507_ = lean_ctor_get(v___y_495_, 2);
v_options_508_ = lean_ctor_get(v_toCold_505_, 2);
lean_inc_ref(v_options_508_);
lean_inc_ref(v_lctx_507_);
v___x_509_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_509_, 0, v_env_503_);
lean_ctor_set(v___x_509_, 1, v_mctx_506_);
lean_ctor_set(v___x_509_, 2, v_lctx_507_);
lean_ctor_set(v___x_509_, 3, v_options_508_);
v___x_510_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v_msgData_494_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_494_ = stack[0].m_obj;
lean_object* v___y_495_ = stack[1].m_obj;
lean_object* v___y_496_ = stack[2].m_obj;
lean_object* v___y_497_ = stack[3].m_obj;
lean_object* v___y_498_ = stack[4].m_obj;
lean_object* v_res_512_;
v_res_512_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msgData_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
stack->m_obj
 = v_res_512_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object* v_msgData_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msgData_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v_res_519_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object* v_msg_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_ref_526_; lean_object* v___x_527_; lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_ref_526_ = lean_ctor_get(v___y_523_, 2);
v___x_527_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
lean_inc(v_ref_526_);
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_ref_526_);
lean_ctor_set(v___x_532_, 1, v_a_528_);
if (v_isShared_531_ == 0)
{
lean_ctor_set_tag(v___x_530_, 1);
lean_ctor_set(v___x_530_, 0, v___x_532_);
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_520_ = stack[0].m_obj;
lean_object* v___y_521_ = stack[1].m_obj;
lean_object* v___y_522_ = stack[2].m_obj;
lean_object* v___y_523_ = stack[3].m_obj;
lean_object* v___y_524_ = stack[4].m_obj;
lean_object* v_res_537_;
v_res_537_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object* v_msg_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
if (lean_obj_tag(v_a_545_) == 0)
{
lean_object* v___x_547_; 
v___x_547_ = l_List_reverse___redArg(v_a_546_);
return v___x_547_;
}
else
{
lean_object* v_head_548_; lean_object* v_tail_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_558_; 
v_head_548_ = lean_ctor_get(v_a_545_, 0);
v_tail_549_ = lean_ctor_get(v_a_545_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_558_ == 0)
{
v___x_551_ = v_a_545_;
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_tail_549_);
lean_inc(v_head_548_);
lean_dec(v_a_545_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = l_Lean_MessageData_ofExpr(v_head_548_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v_a_546_);
lean_ctor_set(v___x_551_, 0, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_a_546_);
v___x_555_ = v_reuseFailAlloc_557_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
v_a_545_ = v_tail_549_;
v_a_546_ = v___x_555_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0));
v___x_561_ = l_Lean_stringToMessageData(v___x_560_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2));
v___x_564_ = l_Lean_stringToMessageData(v___x_563_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4));
v___x_567_ = l_Lean_stringToMessageData(v___x_566_);
return v___x_567_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(lean_object* v_idx_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_varToExpr_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v_varToExpr_577_ = lean_ctor_get(v_a_569_, 2);
v___x_578_ = lean_array_get_size(v_varToExpr_577_);
v___x_579_ = lean_nat_dec_lt(v_idx_568_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
lean_inc_ref(v_varToExpr_577_);
lean_dec_ref(v_a_569_);
v___x_580_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1);
v___x_581_ = l_Nat_reprFast(v_idx_568_);
v___x_582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
v___x_583_ = l_Lean_MessageData_ofFormat(v___x_582_);
v___x_584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_580_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = l_Nat_reprFast(v___x_578_);
v___x_588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
v___x_589_ = l_Lean_MessageData_ofFormat(v___x_588_);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_586_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_array_to_list(v_varToExpr_577_);
v___x_594_ = lean_box(0);
v___x_595_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(v___x_593_, v___x_594_);
v___x_596_ = l_Lean_MessageData_ofList(v___x_595_);
v___x_597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_592_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v___x_597_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
return v___x_598_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_array_fget(v_varToExpr_577_, v_idx_568_);
lean_dec(v_idx_568_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v_a_569_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_idx_568_ = stack[0].m_obj;
lean_object* v_a_569_ = stack[1].m_obj;
lean_object* v_a_570_ = stack[2].m_obj;
lean_object* v_a_571_ = stack[3].m_obj;
lean_object* v_a_572_ = stack[4].m_obj;
lean_object* v_a_573_ = stack[5].m_obj;
lean_object* v_a_574_ = stack[6].m_obj;
lean_object* v_a_575_ = stack[7].m_obj;
lean_object* v_res_602_;
v_res_602_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(v_idx_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
stack->m_obj
 = v_res_602_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___boxed(lean_object* v_idx_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(v_idx_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
return v_res_612_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_object* v_00_u03b1_613_, lean_object* v_msg_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_614_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
return v___x_623_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_614_ = stack[1].m_obj;
lean_object* v___y_615_ = stack[2].m_obj;
lean_object* v___y_616_ = stack[3].m_obj;
lean_object* v___y_617_ = stack[4].m_obj;
lean_object* v___y_618_ = stack[5].m_obj;
lean_object* v___y_619_ = stack[6].m_obj;
lean_object* v___y_620_ = stack[7].m_obj;
lean_object* v___y_621_ = stack[8].m_obj;
lean_object* v_res_624_;
v_res_624_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_box(0), v_msg_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
stack->m_obj
 = v_res_624_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object* v_00_u03b1_625_, lean_object* v_msg_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(v_00_u03b1_625_, v_msg_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec_ref(v___y_627_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object* v_c_636_){
_start:
{
lean_object* v___y_638_; 
if (lean_obj_tag(v_c_636_) == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___y_638_ = v___x_642_;
goto v___jp_637_;
}
else
{
lean_object* v_val_643_; 
v_val_643_ = lean_ctor_get(v_c_636_, 0);
v___y_638_ = v_val_643_;
goto v___jp_637_;
}
v___jp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_unsigned_to_nat(1u);
v___x_640_ = lean_nat_add(v___y_638_, v___x_639_);
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object* v_c_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v_c_644_);
lean_dec(v_c_644_);
return v_res_645_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_box(0);
v___x_647_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object* v_a_648_, lean_object* v_x_649_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
lean_object* v___x_650_; lean_object* v_val_651_; lean_object* v___x_652_; 
v___x_650_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0);
v_val_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_651_);
v___x_652_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_652_, 0, v_a_648_);
lean_ctor_set(v___x_652_, 1, v_val_651_);
lean_ctor_set(v___x_652_, 2, v_x_649_);
return v___x_652_;
}
else
{
lean_object* v_key_653_; lean_object* v_value_654_; lean_object* v_tail_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_670_; 
v_key_653_ = lean_ctor_get(v_x_649_, 0);
v_value_654_ = lean_ctor_get(v_x_649_, 1);
v_tail_655_ = lean_ctor_get(v_x_649_, 2);
v_isSharedCheck_670_ = !lean_is_exclusive(v_x_649_);
if (v_isSharedCheck_670_ == 0)
{
v___x_657_ = v_x_649_;
v_isShared_658_ = v_isSharedCheck_670_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_tail_655_);
lean_inc(v_value_654_);
lean_inc(v_key_653_);
lean_dec(v_x_649_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_670_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint8_t v___x_659_; 
v___x_659_ = lean_nat_dec_eq(v_key_653_, v_a_648_);
if (v___x_659_ == 0)
{
lean_object* v_tail_660_; lean_object* v___x_662_; 
v_tail_660_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_648_, v_tail_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 2, v_tail_660_);
v___x_662_ = v___x_657_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_key_653_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_value_654_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_tail_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_val_666_; lean_object* v___x_668_; 
lean_dec(v_key_653_);
v___x_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_664_, 0, v_value_654_);
v___x_665_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_664_);
lean_dec_ref_known(v___x_664_, 1);
v_val_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_666_);
lean_dec(v___x_665_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_val_666_);
lean_ctor_set(v___x_657_, 0, v_a_648_);
v___x_668_ = v___x_657_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_648_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_val_666_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_tail_655_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
if (lean_obj_tag(v_x_672_) == 0)
{
return v_x_671_;
}
else
{
lean_object* v_key_673_; lean_object* v_value_674_; lean_object* v_tail_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_698_; 
v_key_673_ = lean_ctor_get(v_x_672_, 0);
v_value_674_ = lean_ctor_get(v_x_672_, 1);
v_tail_675_ = lean_ctor_get(v_x_672_, 2);
v_isSharedCheck_698_ = !lean_is_exclusive(v_x_672_);
if (v_isSharedCheck_698_ == 0)
{
v___x_677_ = v_x_672_;
v_isShared_678_ = v_isSharedCheck_698_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_tail_675_);
lean_inc(v_value_674_);
lean_inc(v_key_673_);
lean_dec(v_x_672_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_698_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; uint64_t v___x_680_; uint64_t v___x_681_; uint64_t v___x_682_; uint64_t v_fold_683_; uint64_t v___x_684_; uint64_t v___x_685_; uint64_t v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_679_ = lean_array_get_size(v_x_671_);
v___x_680_ = lean_uint64_of_nat(v_key_673_);
v___x_681_ = 32ULL;
v___x_682_ = lean_uint64_shift_right(v___x_680_, v___x_681_);
v_fold_683_ = lean_uint64_xor(v___x_680_, v___x_682_);
v___x_684_ = 16ULL;
v___x_685_ = lean_uint64_shift_right(v_fold_683_, v___x_684_);
v___x_686_ = lean_uint64_xor(v_fold_683_, v___x_685_);
v___x_687_ = lean_uint64_to_usize(v___x_686_);
v___x_688_ = lean_usize_of_nat(v___x_679_);
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_sub(v___x_688_, v___x_689_);
v___x_691_ = lean_usize_land(v___x_687_, v___x_690_);
v___x_692_ = lean_array_uget_borrowed(v_x_671_, v___x_691_);
lean_inc(v___x_692_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 2, v___x_692_);
v___x_694_ = v___x_677_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_key_673_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_value_674_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v___x_692_);
v___x_694_ = v_reuseFailAlloc_697_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; 
v___x_695_ = lean_array_uset(v_x_671_, v___x_691_, v___x_694_);
v_x_671_ = v___x_695_;
v_x_672_ = v_tail_675_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_699_, lean_object* v_source_700_, lean_object* v_target_701_){
_start:
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_array_get_size(v_source_700_);
v___x_703_ = lean_nat_dec_lt(v_i_699_, v___x_702_);
if (v___x_703_ == 0)
{
lean_dec_ref(v_source_700_);
lean_dec(v_i_699_);
return v_target_701_;
}
else
{
lean_object* v_es_704_; lean_object* v___x_705_; lean_object* v_source_706_; lean_object* v_target_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_es_704_ = lean_array_fget(v_source_700_, v_i_699_);
v___x_705_ = lean_box(0);
v_source_706_ = lean_array_fset(v_source_700_, v_i_699_, v___x_705_);
v_target_707_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_701_, v_es_704_);
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_nat_add(v_i_699_, v___x_708_);
lean_dec(v_i_699_);
v_i_699_ = v___x_709_;
v_source_700_ = v_source_706_;
v_target_701_ = v_target_707_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object* v_data_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_nbuckets_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_712_ = lean_array_get_size(v_data_711_);
v___x_713_ = lean_unsigned_to_nat(2u);
v_nbuckets_714_ = lean_nat_mul(v___x_712_, v___x_713_);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_box(0);
v___x_717_ = lean_mk_array(v_nbuckets_714_, v___x_716_);
v___x_718_ = lean_array_propagate_mark(v_data_711_, v___x_717_);
v___x_719_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v___x_715_, v_data_711_, v___x_718_);
return v___x_719_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object* v_a_720_, lean_object* v_x_721_){
_start:
{
if (lean_obj_tag(v_x_721_) == 0)
{
uint8_t v___x_722_; 
v___x_722_ = 0;
return v___x_722_;
}
else
{
lean_object* v_key_723_; lean_object* v_tail_724_; uint8_t v___x_725_; 
v_key_723_ = lean_ctor_get(v_x_721_, 0);
v_tail_724_ = lean_ctor_get(v_x_721_, 2);
v___x_725_ = lean_nat_dec_eq(v_key_723_, v_a_720_);
if (v___x_725_ == 0)
{
v_x_721_ = v_tail_724_;
goto _start;
}
else
{
return v___x_725_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_720_ = stack[0].m_obj;
lean_object* v_x_721_ = stack[1].m_obj;
uint8_t v_res_727_;
v_res_727_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_720_, v_x_721_);
stack->m_num = v_res_727_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_728_, lean_object* v_x_729_){
_start:
{
uint8_t v_res_730_; lean_object* v_r_731_; 
v_res_730_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_728_, v_x_729_);
lean_dec(v_x_729_);
lean_dec(v_a_728_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object* v_m_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_size_734_; lean_object* v_buckets_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_783_; 
v_size_734_ = lean_ctor_get(v_m_732_, 0);
v_buckets_735_ = lean_ctor_get(v_m_732_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_m_732_);
if (v_isSharedCheck_783_ == 0)
{
v___x_737_ = v_m_732_;
v_isShared_738_ = v_isSharedCheck_783_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_buckets_735_);
lean_inc(v_size_734_);
lean_dec(v_m_732_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_783_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; uint64_t v___x_740_; uint64_t v___x_741_; uint64_t v___x_742_; uint64_t v_fold_743_; uint64_t v___x_744_; uint64_t v___x_745_; uint64_t v___x_746_; size_t v___x_747_; size_t v___x_748_; size_t v___x_749_; size_t v___x_750_; size_t v___x_751_; lean_object* v_bkt_752_; uint8_t v___x_753_; 
v___x_739_ = lean_array_get_size(v_buckets_735_);
v___x_740_ = lean_uint64_of_nat(v_a_733_);
v___x_741_ = 32ULL;
v___x_742_ = lean_uint64_shift_right(v___x_740_, v___x_741_);
v_fold_743_ = lean_uint64_xor(v___x_740_, v___x_742_);
v___x_744_ = 16ULL;
v___x_745_ = lean_uint64_shift_right(v_fold_743_, v___x_744_);
v___x_746_ = lean_uint64_xor(v_fold_743_, v___x_745_);
v___x_747_ = lean_uint64_to_usize(v___x_746_);
v___x_748_ = lean_usize_of_nat(v___x_739_);
v___x_749_ = ((size_t)1ULL);
v___x_750_ = lean_usize_sub(v___x_748_, v___x_749_);
v___x_751_ = lean_usize_land(v___x_747_, v___x_750_);
v_bkt_752_ = lean_array_uget_borrowed(v_buckets_735_, v___x_751_);
v___x_753_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_733_, v_bkt_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v_size_x27_755_; lean_object* v___x_756_; lean_object* v_buckets_x27_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_754_ = lean_unsigned_to_nat(1u);
v_size_x27_755_ = lean_nat_add(v_size_734_, v___x_754_);
lean_dec(v_size_734_);
lean_inc(v_bkt_752_);
v___x_756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_756_, 0, v_a_733_);
lean_ctor_set(v___x_756_, 1, v___x_754_);
lean_ctor_set(v___x_756_, 2, v_bkt_752_);
v_buckets_x27_757_ = lean_array_uset(v_buckets_735_, v___x_751_, v___x_756_);
v___x_758_ = lean_unsigned_to_nat(4u);
v___x_759_ = lean_nat_mul(v_size_x27_755_, v___x_758_);
v___x_760_ = lean_unsigned_to_nat(3u);
v___x_761_ = lean_nat_div(v___x_759_, v___x_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_array_get_size(v_buckets_x27_757_);
v___x_763_ = lean_nat_dec_le(v___x_761_, v___x_762_);
lean_dec(v___x_761_);
if (v___x_763_ == 0)
{
lean_object* v_val_764_; lean_object* v___x_766_; 
v_val_764_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_757_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v_val_764_);
lean_ctor_set(v___x_737_, 0, v_size_x27_755_);
v___x_766_ = v___x_737_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_size_x27_755_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_val_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
else
{
lean_object* v___x_769_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v_buckets_x27_757_);
lean_ctor_set(v___x_737_, 0, v_size_x27_755_);
v___x_769_ = v___x_737_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_size_x27_755_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_buckets_x27_757_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
else
{
lean_object* v___x_771_; lean_object* v_buckets_x27_772_; lean_object* v_bkt_x27_773_; lean_object* v___y_775_; uint8_t v___x_780_; 
lean_inc(v_bkt_752_);
v___x_771_ = lean_box(0);
v_buckets_x27_772_ = lean_array_uset(v_buckets_735_, v___x_751_, v___x_771_);
lean_inc(v_a_733_);
v_bkt_x27_773_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_733_, v_bkt_752_);
v___x_780_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_733_, v_bkt_x27_773_);
lean_dec(v_a_733_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_sub(v_size_734_, v___x_781_);
lean_dec(v_size_734_);
v___y_775_ = v___x_782_;
goto v___jp_774_;
}
else
{
v___y_775_ = v_size_734_;
goto v___jp_774_;
}
v___jp_774_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = lean_array_uset(v_buckets_x27_772_, v___x_751_, v_bkt_x27_773_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v___x_776_);
lean_ctor_set(v___x_737_, 0, v___y_775_);
v___x_778_ = v___x_737_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___y_775_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object* v_coeff_784_, lean_object* v_e_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_788_; lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_806_; 
v___x_788_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_785_, v_a_786_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_806_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_806_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_806_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_fst_793_; lean_object* v_snd_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_805_; 
v_fst_793_ = lean_ctor_get(v_a_789_, 0);
v_snd_794_ = lean_ctor_get(v_a_789_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_a_789_);
if (v_isSharedCheck_805_ == 0)
{
v___x_796_ = v_a_789_;
v_isShared_797_ = v_isSharedCheck_805_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_snd_794_);
lean_inc(v_fst_793_);
lean_dec(v_a_789_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_805_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(v_coeff_784_, v_fst_793_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_snd_794_);
v___x_800_ = v_reuseFailAlloc_804_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_800_);
v___x_802_ = v___x_791_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_coeff_784_ = stack[0].m_obj;
lean_object* v_e_785_ = stack[1].m_obj;
lean_object* v_a_786_ = stack[2].m_obj;
lean_object* v_res_807_;
v_res_807_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_784_, v_e_785_, v_a_786_);
stack->m_obj
 = v_res_807_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object* v_coeff_808_, lean_object* v_e_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_808_, v_e_809_, v_a_810_);
return v_res_812_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object* v_coeff_813_, lean_object* v_e_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_813_, v_e_814_, v_a_815_);
return v___x_823_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_coeff_813_ = stack[0].m_obj;
lean_object* v_e_814_ = stack[1].m_obj;
lean_object* v_a_815_ = stack[2].m_obj;
lean_object* v_a_816_ = stack[3].m_obj;
lean_object* v_a_817_ = stack[4].m_obj;
lean_object* v_a_818_ = stack[5].m_obj;
lean_object* v_a_819_ = stack[6].m_obj;
lean_object* v_a_820_ = stack[7].m_obj;
lean_object* v_a_821_ = stack[8].m_obj;
lean_object* v_res_824_;
v_res_824_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(v_coeff_813_, v_e_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object* v_coeff_825_, lean_object* v_e_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(v_coeff_825_, v_e_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_835_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object* v_00_u03b2_836_, lean_object* v_a_837_, lean_object* v_x_838_){
_start:
{
uint8_t v___x_839_; 
v___x_839_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_837_, v_x_838_);
return v___x_839_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_837_ = stack[1].m_obj;
lean_object* v_x_838_ = stack[2].m_obj;
uint8_t v_res_840_;
v_res_840_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_box(0), v_a_837_, v_x_838_);
stack->m_num = v_res_840_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_841_, lean_object* v_a_842_, lean_object* v_x_843_){
_start:
{
uint8_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(v_00_u03b2_841_, v_a_842_, v_x_843_);
lean_dec(v_x_843_);
lean_dec(v_a_842_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object* v_00_u03b2_846_, lean_object* v_data_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_data_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_849_, lean_object* v_i_850_, lean_object* v_source_851_, lean_object* v_target_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v_i_850_, v_source_851_, v_target_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_854_, lean_object* v_x_855_, lean_object* v_x_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_855_, v_x_856_);
return v___x_857_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_858_; double v___x_859_; 
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_float_of_nat(v___x_858_);
return v___x_859_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(lean_object* v_cls_863_, lean_object* v_msg_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_ref_871_; lean_object* v___x_872_; lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_919_; 
v_ref_871_ = lean_ctor_get(v___y_868_, 2);
v___x_872_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_864_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_919_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_919_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_919_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v_traceState_878_; lean_object* v_env_879_; lean_object* v_nextMacroScope_880_; lean_object* v_ngen_881_; lean_object* v_auxDeclNGen_882_; lean_object* v_cache_883_; lean_object* v_recordedDeps_884_; lean_object* v_messages_885_; lean_object* v_infoState_886_; lean_object* v_snapshotTasks_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_918_; 
v___x_877_ = lean_st_ref_take(v___y_869_);
v_traceState_878_ = lean_ctor_get(v___x_877_, 4);
v_env_879_ = lean_ctor_get(v___x_877_, 0);
v_nextMacroScope_880_ = lean_ctor_get(v___x_877_, 1);
v_ngen_881_ = lean_ctor_get(v___x_877_, 2);
v_auxDeclNGen_882_ = lean_ctor_get(v___x_877_, 3);
v_cache_883_ = lean_ctor_get(v___x_877_, 5);
v_recordedDeps_884_ = lean_ctor_get(v___x_877_, 6);
v_messages_885_ = lean_ctor_get(v___x_877_, 7);
v_infoState_886_ = lean_ctor_get(v___x_877_, 8);
v_snapshotTasks_887_ = lean_ctor_get(v___x_877_, 9);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_918_ == 0)
{
v___x_889_ = v___x_877_;
v_isShared_890_ = v_isSharedCheck_918_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_snapshotTasks_887_);
lean_inc(v_infoState_886_);
lean_inc(v_messages_885_);
lean_inc(v_recordedDeps_884_);
lean_inc(v_cache_883_);
lean_inc(v_traceState_878_);
lean_inc(v_auxDeclNGen_882_);
lean_inc(v_ngen_881_);
lean_inc(v_nextMacroScope_880_);
lean_inc(v_env_879_);
lean_dec(v___x_877_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_918_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint64_t v_tid_891_; lean_object* v_traces_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_917_; 
v_tid_891_ = lean_ctor_get_uint64(v_traceState_878_, sizeof(void*)*1);
v_traces_892_ = lean_ctor_get(v_traceState_878_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_traceState_878_);
if (v_isSharedCheck_917_ == 0)
{
v___x_894_ = v_traceState_878_;
v_isShared_895_ = v_isSharedCheck_917_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_traces_892_);
lean_dec(v_traceState_878_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_917_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_897_; double v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_896_ = lean_box(0);
v___x_897_ = lean_box(0);
v___x_898_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_899_ = 0;
v___x_900_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_901_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_901_, 0, v_cls_863_);
lean_ctor_set(v___x_901_, 1, v___x_897_);
lean_ctor_set(v___x_901_, 2, v___x_900_);
lean_ctor_set_float(v___x_901_, sizeof(void*)*3, v___x_898_);
lean_ctor_set_float(v___x_901_, sizeof(void*)*3 + 8, v___x_898_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*3 + 16, v___x_899_);
v___x_902_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_903_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v_a_873_);
lean_ctor_set(v___x_903_, 2, v___x_902_);
lean_inc(v_ref_871_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v_ref_871_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Lean_PersistentArray_push___redArg(v_traces_892_, v___x_904_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_905_);
v___x_907_ = v___x_894_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_905_);
lean_ctor_set_uint64(v_reuseFailAlloc_916_, sizeof(void*)*1, v_tid_891_);
v___x_907_ = v_reuseFailAlloc_916_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_909_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 4, v___x_907_);
v___x_909_ = v___x_889_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_env_879_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_nextMacroScope_880_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_ngen_881_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_auxDeclNGen_882_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_915_, 5, v_cache_883_);
lean_ctor_set(v_reuseFailAlloc_915_, 6, v_recordedDeps_884_);
lean_ctor_set(v_reuseFailAlloc_915_, 7, v_messages_885_);
lean_ctor_set(v_reuseFailAlloc_915_, 8, v_infoState_886_);
lean_ctor_set(v_reuseFailAlloc_915_, 9, v_snapshotTasks_887_);
v___x_909_ = v_reuseFailAlloc_915_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_910_ = lean_st_ref_put(v___y_869_, v___x_909_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_896_);
lean_ctor_set(v___x_911_, 1, v___y_865_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_911_);
v___x_913_ = v___x_875_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_863_ = stack[0].m_obj;
lean_object* v_msg_864_ = stack[1].m_obj;
lean_object* v___y_865_ = stack[2].m_obj;
lean_object* v___y_866_ = stack[3].m_obj;
lean_object* v___y_867_ = stack[4].m_obj;
lean_object* v___y_868_ = stack[5].m_obj;
lean_object* v___y_869_ = stack[6].m_obj;
lean_object* v_res_920_;
v_res_920_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_863_, v_msg_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
stack->m_obj
 = v_res_920_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___boxed(lean_object* v_cls_921_, lean_object* v_msg_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_921_, v_msg_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_929_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6(void){
_start:
{
lean_object* v_cls_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v_cls_940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_942_ = l_Lean_Name_append(v___x_941_, v_cls_940_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9));
v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_955_, lean_object* v_coeff_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
if (lean_obj_tag(v_a_957_) == 5)
{
lean_object* v_fn_966_; 
v_fn_966_ = lean_ctor_get(v_a_957_, 0);
if (lean_obj_tag(v_fn_966_) == 5)
{
lean_object* v_arg_967_; lean_object* v_fn_968_; lean_object* v_arg_969_; uint8_t v___x_970_; 
v_arg_967_ = lean_ctor_get(v_a_957_, 1);
v_fn_968_ = lean_ctor_get(v_fn_966_, 0);
v_arg_969_ = lean_ctor_get(v_fn_966_, 1);
lean_inc_ref(v_fn_968_);
v___x_970_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_fn_968_);
if (v___x_970_ == 0)
{
lean_object* v_toCold_971_; lean_object* v_options_972_; uint8_t v_hasTrace_973_; 
v_toCold_971_ = lean_ctor_get(v_a_963_, 0);
v_options_972_ = lean_ctor_get(v_toCold_971_, 2);
v_hasTrace_973_ = lean_ctor_get_uint8(v_options_972_, sizeof(void*)*1);
if (v_hasTrace_973_ == 0)
{
lean_object* v___x_974_; 
lean_dec_ref(v_op_955_);
v___x_974_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_956_, v_a_957_, v_a_958_);
return v___x_974_;
}
else
{
lean_object* v_inheritedTraceOptions_975_; lean_object* v_cls_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_inheritedTraceOptions_975_ = lean_ctor_get(v_toCold_971_, 11);
v_cls_976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_977_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_978_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_975_, v_options_972_, v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
lean_dec_ref(v_op_955_);
v___x_979_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_956_, v_a_957_, v_a_958_);
return v___x_979_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_980_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_968_);
v___x_981_ = l_Lean_MessageData_ofExpr(v_fn_968_);
v___x_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
lean_inc_ref(v_arg_969_);
v___x_985_ = l_Lean_MessageData_ofExpr(v_arg_969_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_983_);
lean_inc_ref(v_arg_967_);
v___x_988_ = l_Lean_MessageData_ofExpr(v_arg_967_);
v___x_989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_955_);
v___x_993_ = l_Lean_MessageData_ofExpr(v___x_992_);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_991_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_976_, v___x_996_, v_a_958_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v_snd_999_; lean_object* v___x_1000_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v_snd_999_ = lean_ctor_get(v_a_998_, 1);
lean_inc(v_snd_999_);
lean_dec(v_a_998_);
v___x_1000_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_956_, v_a_957_, v_snd_999_);
return v___x_1000_;
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref_known(v_a_957_, 2);
lean_dec_ref(v_coeff_956_);
v_a_1001_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_997_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_997_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
else
{
lean_object* v___x_1009_; 
lean_inc_ref(v_arg_969_);
lean_inc_ref(v_arg_967_);
lean_dec_ref_known(v_a_957_, 2);
lean_inc_ref(v_op_955_);
v___x_1009_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_955_, v_coeff_956_, v_arg_969_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v_fst_1011_; lean_object* v_snd_1012_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v_fst_1011_ = lean_ctor_get(v_a_1010_, 0);
lean_inc(v_fst_1011_);
v_snd_1012_ = lean_ctor_get(v_a_1010_, 1);
lean_inc(v_snd_1012_);
lean_dec(v_a_1010_);
v_coeff_956_ = v_fst_1011_;
v_a_957_ = v_arg_967_;
v_a_958_ = v_snd_1012_;
goto _start;
}
else
{
lean_dec_ref(v_arg_967_);
lean_dec_ref(v_op_955_);
return v___x_1009_;
}
}
}
else
{
lean_object* v___x_1014_; 
lean_dec_ref(v_op_955_);
v___x_1014_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_956_, v_a_957_, v_a_958_);
return v___x_1014_;
}
}
else
{
lean_object* v___x_1015_; 
lean_dec_ref(v_op_955_);
v___x_1015_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_956_, v_a_957_, v_a_958_);
return v___x_1015_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_955_ = stack[0].m_obj;
lean_object* v_coeff_956_ = stack[1].m_obj;
lean_object* v_a_957_ = stack[2].m_obj;
lean_object* v_a_958_ = stack[3].m_obj;
lean_object* v_a_959_ = stack[4].m_obj;
lean_object* v_a_960_ = stack[5].m_obj;
lean_object* v_a_961_ = stack[6].m_obj;
lean_object* v_a_962_ = stack[7].m_obj;
lean_object* v_a_963_ = stack[8].m_obj;
lean_object* v_a_964_ = stack[9].m_obj;
lean_object* v_res_1016_;
v_res_1016_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_955_, v_coeff_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
stack->m_obj
 = v_res_1016_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_1017_, lean_object* v_coeff_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1017_, v_coeff_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
return v_res_1028_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_1029_, lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_1029_, v_msg_1030_, v___y_1031_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1029_ = stack[0].m_obj;
lean_object* v_msg_1030_ = stack[1].m_obj;
lean_object* v___y_1031_ = stack[2].m_obj;
lean_object* v___y_1032_ = stack[3].m_obj;
lean_object* v___y_1033_ = stack[4].m_obj;
lean_object* v___y_1034_ = stack[5].m_obj;
lean_object* v___y_1035_ = stack[6].m_obj;
lean_object* v___y_1036_ = stack[7].m_obj;
lean_object* v___y_1037_ = stack[8].m_obj;
lean_object* v_res_1040_;
v_res_1040_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_1029_, v_msg_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
stack->m_obj
 = v_res_1040_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_1041_, lean_object* v_msg_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_1041_, v_msg_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1051_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_unsigned_to_nat(16u);
v___x_1054_ = lean_mk_array(v___x_1053_, v___x_1052_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1055_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_1055_);
return v___x_1057_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object* v_op_1058_, lean_object* v_e_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1069_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1058_, v___x_1068_, v_e_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1069_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_1058_ = stack[0].m_obj;
lean_object* v_e_1059_ = stack[1].m_obj;
lean_object* v_a_1060_ = stack[2].m_obj;
lean_object* v_a_1061_ = stack[3].m_obj;
lean_object* v_a_1062_ = stack[4].m_obj;
lean_object* v_a_1063_ = stack[5].m_obj;
lean_object* v_a_1064_ = stack[6].m_obj;
lean_object* v_a_1065_ = stack[7].m_obj;
lean_object* v_a_1066_ = stack[8].m_obj;
lean_object* v_res_1070_;
v_res_1070_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_op_1058_, v_e_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
stack->m_obj
 = v_res_1070_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_1071_, lean_object* v_e_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_op_1071_, v_e_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1082_, lean_object* v_x_1083_){
_start:
{
if (lean_obj_tag(v_x_1083_) == 0)
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_box(0);
return v___x_1084_;
}
else
{
lean_object* v_key_1085_; lean_object* v_value_1086_; lean_object* v_tail_1087_; uint8_t v___x_1088_; 
v_key_1085_ = lean_ctor_get(v_x_1083_, 0);
v_value_1086_ = lean_ctor_get(v_x_1083_, 1);
v_tail_1087_ = lean_ctor_get(v_x_1083_, 2);
v___x_1088_ = lean_nat_dec_eq(v_key_1085_, v_a_1082_);
if (v___x_1088_ == 0)
{
v_x_1083_ = v_tail_1087_;
goto _start;
}
else
{
lean_object* v___x_1090_; 
lean_inc(v_value_1086_);
v___x_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_value_1086_);
return v___x_1090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1091_, lean_object* v_x_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1091_, v_x_1092_);
lean_dec(v_x_1092_);
lean_dec(v_a_1091_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_buckets_1096_; lean_object* v___x_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; uint64_t v_fold_1101_; uint64_t v___x_1102_; uint64_t v___x_1103_; uint64_t v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v_buckets_1096_ = lean_ctor_get(v_m_1094_, 1);
v___x_1097_ = lean_array_get_size(v_buckets_1096_);
v___x_1098_ = lean_uint64_of_nat(v_a_1095_);
v___x_1099_ = 32ULL;
v___x_1100_ = lean_uint64_shift_right(v___x_1098_, v___x_1099_);
v_fold_1101_ = lean_uint64_xor(v___x_1098_, v___x_1100_);
v___x_1102_ = 16ULL;
v___x_1103_ = lean_uint64_shift_right(v_fold_1101_, v___x_1102_);
v___x_1104_ = lean_uint64_xor(v_fold_1101_, v___x_1103_);
v___x_1105_ = lean_uint64_to_usize(v___x_1104_);
v___x_1106_ = lean_usize_of_nat(v___x_1097_);
v___x_1107_ = ((size_t)1ULL);
v___x_1108_ = lean_usize_sub(v___x_1106_, v___x_1107_);
v___x_1109_ = lean_usize_land(v___x_1105_, v___x_1108_);
v___x_1110_ = lean_array_uget_borrowed(v_buckets_1096_, v___x_1109_);
v___x_1111_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1095_, v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_m_1112_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1115_, lean_object* v_b_1116_, lean_object* v_x_1117_){
_start:
{
if (lean_obj_tag(v_x_1117_) == 0)
{
lean_dec(v_b_1116_);
lean_dec(v_a_1115_);
return v_x_1117_;
}
else
{
lean_object* v_key_1118_; lean_object* v_value_1119_; lean_object* v_tail_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1132_; 
v_key_1118_ = lean_ctor_get(v_x_1117_, 0);
v_value_1119_ = lean_ctor_get(v_x_1117_, 1);
v_tail_1120_ = lean_ctor_get(v_x_1117_, 2);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_x_1117_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1122_ = v_x_1117_;
v_isShared_1123_ = v_isSharedCheck_1132_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_tail_1120_);
lean_inc(v_value_1119_);
lean_inc(v_key_1118_);
lean_dec(v_x_1117_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1132_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_nat_dec_eq(v_key_1118_, v_a_1115_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1115_, v_b_1116_, v_tail_1120_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 2, v___x_1125_);
v___x_1127_ = v___x_1122_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_key_1118_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_value_1119_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
else
{
lean_object* v___x_1130_; 
lean_dec(v_value_1119_);
lean_dec(v_key_1118_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v_b_1116_);
lean_ctor_set(v___x_1122_, 0, v_a_1115_);
v___x_1130_ = v___x_1122_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1115_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_b_1116_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v_tail_1120_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1133_, lean_object* v_a_1134_, lean_object* v_b_1135_){
_start:
{
lean_object* v_size_1136_; lean_object* v_buckets_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1180_; 
v_size_1136_ = lean_ctor_get(v_m_1133_, 0);
v_buckets_1137_ = lean_ctor_get(v_m_1133_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_m_1133_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1139_ = v_m_1133_;
v_isShared_1140_ = v_isSharedCheck_1180_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_buckets_1137_);
lean_inc(v_size_1136_);
lean_dec(v_m_1133_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1180_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; uint64_t v___x_1142_; uint64_t v___x_1143_; uint64_t v___x_1144_; uint64_t v_fold_1145_; uint64_t v___x_1146_; uint64_t v___x_1147_; uint64_t v___x_1148_; size_t v___x_1149_; size_t v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; lean_object* v_bkt_1154_; uint8_t v___x_1155_; 
v___x_1141_ = lean_array_get_size(v_buckets_1137_);
v___x_1142_ = lean_uint64_of_nat(v_a_1134_);
v___x_1143_ = 32ULL;
v___x_1144_ = lean_uint64_shift_right(v___x_1142_, v___x_1143_);
v_fold_1145_ = lean_uint64_xor(v___x_1142_, v___x_1144_);
v___x_1146_ = 16ULL;
v___x_1147_ = lean_uint64_shift_right(v_fold_1145_, v___x_1146_);
v___x_1148_ = lean_uint64_xor(v_fold_1145_, v___x_1147_);
v___x_1149_ = lean_uint64_to_usize(v___x_1148_);
v___x_1150_ = lean_usize_of_nat(v___x_1141_);
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_sub(v___x_1150_, v___x_1151_);
v___x_1153_ = lean_usize_land(v___x_1149_, v___x_1152_);
v_bkt_1154_ = lean_array_uget_borrowed(v_buckets_1137_, v___x_1153_);
v___x_1155_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1134_, v_bkt_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v_size_x27_1157_; lean_object* v___x_1158_; lean_object* v_buckets_x27_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
v_size_x27_1157_ = lean_nat_add(v_size_1136_, v___x_1156_);
lean_dec(v_size_1136_);
lean_inc(v_bkt_1154_);
v___x_1158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1158_, 0, v_a_1134_);
lean_ctor_set(v___x_1158_, 1, v_b_1135_);
lean_ctor_set(v___x_1158_, 2, v_bkt_1154_);
v_buckets_x27_1159_ = lean_array_uset(v_buckets_1137_, v___x_1153_, v___x_1158_);
v___x_1160_ = lean_unsigned_to_nat(4u);
v___x_1161_ = lean_nat_mul(v_size_x27_1157_, v___x_1160_);
v___x_1162_ = lean_unsigned_to_nat(3u);
v___x_1163_ = lean_nat_div(v___x_1161_, v___x_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_array_get_size(v_buckets_x27_1159_);
v___x_1165_ = lean_nat_dec_le(v___x_1163_, v___x_1164_);
lean_dec(v___x_1163_);
if (v___x_1165_ == 0)
{
lean_object* v_val_1166_; lean_object* v___x_1168_; 
v_val_1166_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1159_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v_val_1166_);
lean_ctor_set(v___x_1139_, 0, v_size_x27_1157_);
v___x_1168_ = v___x_1139_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_size_x27_1157_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_val_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
else
{
lean_object* v___x_1171_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v_buckets_x27_1159_);
lean_ctor_set(v___x_1139_, 0, v_size_x27_1157_);
v___x_1171_ = v___x_1139_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_size_x27_1157_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_buckets_x27_1159_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
else
{
lean_object* v___x_1173_; lean_object* v_buckets_x27_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_inc(v_bkt_1154_);
v___x_1173_ = lean_box(0);
v_buckets_x27_1174_ = lean_array_uset(v_buckets_1137_, v___x_1153_, v___x_1173_);
v___x_1175_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1134_, v_b_1135_, v_bkt_1154_);
v___x_1176_ = lean_array_uset(v_buckets_x27_1174_, v___x_1153_, v___x_1175_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1176_);
v___x_1178_ = v___x_1139_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_size_1136_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_){
_start:
{
if (lean_obj_tag(v_x_1183_) == 0)
{
return v_x_1182_;
}
else
{
lean_object* v_key_1184_; lean_object* v_value_1185_; lean_object* v_tail_1186_; lean_object* v___y_1188_; lean_object* v___x_1191_; 
v_key_1184_ = lean_ctor_get(v_x_1183_, 0);
lean_inc(v_key_1184_);
v_value_1185_ = lean_ctor_get(v_x_1183_, 1);
lean_inc(v_value_1185_);
v_tail_1186_ = lean_ctor_get(v_x_1183_, 2);
lean_inc(v_tail_1186_);
lean_dec_ref_known(v_x_1183_, 3);
v___x_1191_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1181_, v_key_1184_);
if (lean_obj_tag(v___x_1191_) == 1)
{
lean_object* v_val_1192_; uint8_t v___x_1193_; 
v_val_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_val_1192_);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1193_ = lean_nat_dec_le(v_value_1185_, v_val_1192_);
if (v___x_1193_ == 0)
{
lean_dec(v_value_1185_);
v___y_1188_ = v_val_1192_;
goto v___jp_1187_;
}
else
{
lean_dec(v_val_1192_);
v___y_1188_ = v_value_1185_;
goto v___jp_1187_;
}
}
else
{
lean_dec(v___x_1191_);
lean_dec(v_value_1185_);
lean_dec(v_key_1184_);
v_x_1183_ = v_tail_1186_;
goto _start;
}
v___jp_1187_:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1182_, v_key_1184_, v___y_1188_);
v_x_1182_ = v___x_1189_;
v_x_1183_ = v_tail_1186_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1195_, v_x_1196_, v_x_1197_);
lean_dec_ref(v_snd_1195_);
return v_res_1198_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1199_, lean_object* v_as_1200_, size_t v_i_1201_, size_t v_stop_1202_, lean_object* v_b_1203_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_usize_dec_eq(v_i_1201_, v_stop_1202_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; 
v___x_1205_ = lean_array_uget_borrowed(v_as_1200_, v_i_1201_);
lean_inc(v___x_1205_);
v___x_1206_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1199_, v_b_1203_, v___x_1205_);
v___x_1207_ = ((size_t)1ULL);
v___x_1208_ = lean_usize_add(v_i_1201_, v___x_1207_);
v_i_1201_ = v___x_1208_;
v_b_1203_ = v___x_1206_;
goto _start;
}
else
{
return v_b_1203_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_1199_ = stack[0].m_obj;
lean_object* v_as_1200_ = stack[1].m_obj;
size_t v_i_1201_ = stack[2].m_num;
size_t v_stop_1202_ = stack[3].m_num;
lean_object* v_b_1203_ = stack[4].m_obj;
lean_object* v_res_1210_;
v_res_1210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1199_, v_as_1200_, v_i_1201_, v_stop_1202_, v_b_1203_);
stack->m_obj
 = v_res_1210_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1211_, lean_object* v_as_1212_, lean_object* v_i_1213_, lean_object* v_stop_1214_, lean_object* v_b_1215_){
_start:
{
size_t v_i_boxed_1216_; size_t v_stop_boxed_1217_; lean_object* v_res_1218_; 
v_i_boxed_1216_ = lean_unbox_usize(v_i_1213_);
lean_dec(v_i_1213_);
v_stop_boxed_1217_ = lean_unbox_usize(v_stop_1214_);
lean_dec(v_stop_1214_);
v_res_1218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1211_, v_as_1212_, v_i_boxed_1216_, v_stop_boxed_1217_, v_b_1215_);
lean_dec_ref(v_as_1212_);
lean_dec_ref(v_snd_1211_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1219_, lean_object* v_a_1220_, lean_object* v_x_1221_){
_start:
{
if (lean_obj_tag(v_x_1221_) == 0)
{
lean_dec(v_a_1220_);
return v_x_1221_;
}
else
{
lean_object* v_key_1222_; lean_object* v_value_1223_; lean_object* v_tail_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1237_; 
v_key_1222_ = lean_ctor_get(v_x_1221_, 0);
v_value_1223_ = lean_ctor_get(v_x_1221_, 1);
v_tail_1224_ = lean_ctor_get(v_x_1221_, 2);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_x_1221_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1226_ = v_x_1221_;
v_isShared_1227_ = v_isSharedCheck_1237_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_tail_1224_);
lean_inc(v_value_1223_);
lean_inc(v_key_1222_);
lean_dec(v_x_1221_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1237_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
uint8_t v___x_1228_; 
v___x_1228_ = lean_nat_dec_eq(v_key_1222_, v_a_1220_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1219_, v_a_1220_, v_tail_1224_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 2, v___x_1229_);
v___x_1231_ = v___x_1226_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_key_1222_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_value_1223_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
lean_dec(v_key_1222_);
v___x_1233_ = lean_nat_sub(v_value_1223_, v_commonCnt_1219_);
lean_dec(v_value_1223_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1233_);
lean_ctor_set(v___x_1226_, 0, v_a_1220_);
v___x_1235_ = v___x_1226_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1220_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_tail_1224_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1238_, lean_object* v_a_1239_, lean_object* v_x_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1238_, v_a_1239_, v_x_1240_);
lean_dec(v_commonCnt_1238_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1242_, lean_object* v_m_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_size_1245_; lean_object* v_buckets_1246_; lean_object* v___x_1247_; uint64_t v___x_1248_; uint64_t v___x_1249_; uint64_t v___x_1250_; uint64_t v_fold_1251_; uint64_t v___x_1252_; uint64_t v___x_1253_; uint64_t v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; lean_object* v_bucket_1260_; uint8_t v___x_1261_; 
v_size_1245_ = lean_ctor_get(v_m_1243_, 0);
v_buckets_1246_ = lean_ctor_get(v_m_1243_, 1);
v___x_1247_ = lean_array_get_size(v_buckets_1246_);
v___x_1248_ = lean_uint64_of_nat(v_a_1244_);
v___x_1249_ = 32ULL;
v___x_1250_ = lean_uint64_shift_right(v___x_1248_, v___x_1249_);
v_fold_1251_ = lean_uint64_xor(v___x_1248_, v___x_1250_);
v___x_1252_ = 16ULL;
v___x_1253_ = lean_uint64_shift_right(v_fold_1251_, v___x_1252_);
v___x_1254_ = lean_uint64_xor(v_fold_1251_, v___x_1253_);
v___x_1255_ = lean_uint64_to_usize(v___x_1254_);
v___x_1256_ = lean_usize_of_nat(v___x_1247_);
v___x_1257_ = ((size_t)1ULL);
v___x_1258_ = lean_usize_sub(v___x_1256_, v___x_1257_);
v___x_1259_ = lean_usize_land(v___x_1255_, v___x_1258_);
v_bucket_1260_ = lean_array_uget_borrowed(v_buckets_1246_, v___x_1259_);
v___x_1261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1244_, v_bucket_1260_);
if (v___x_1261_ == 0)
{
lean_dec(v_a_1244_);
return v_m_1243_;
}
else
{
lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1272_; 
lean_inc(v_bucket_1260_);
lean_inc_ref(v_buckets_1246_);
lean_inc(v_size_1245_);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_m_1243_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; lean_object* v_unused_1274_; 
v_unused_1273_ = lean_ctor_get(v_m_1243_, 1);
lean_dec(v_unused_1273_);
v_unused_1274_ = lean_ctor_get(v_m_1243_, 0);
lean_dec(v_unused_1274_);
v___x_1263_ = v_m_1243_;
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
else
{
lean_dec(v_m_1243_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v_buckets_1266_; lean_object* v_bucket_1267_; lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1265_ = lean_box(0);
v_buckets_1266_ = lean_array_uset(v_buckets_1246_, v___x_1259_, v___x_1265_);
v_bucket_1267_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1242_, v_a_1244_, v_bucket_1260_);
v___x_1268_ = lean_array_uset(v_buckets_1266_, v___x_1259_, v_bucket_1267_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v___x_1268_);
v___x_1270_ = v___x_1263_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_size_1245_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1275_, lean_object* v_m_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1275_, v_m_1276_, v_a_1277_);
lean_dec(v_commonCnt_1275_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
if (lean_obj_tag(v_x_1280_) == 0)
{
return v_x_1279_;
}
else
{
lean_object* v_key_1281_; lean_object* v_value_1282_; lean_object* v_tail_1283_; lean_object* v___x_1284_; 
v_key_1281_ = lean_ctor_get(v_x_1280_, 0);
lean_inc(v_key_1281_);
v_value_1282_ = lean_ctor_get(v_x_1280_, 1);
lean_inc(v_value_1282_);
v_tail_1283_ = lean_ctor_get(v_x_1280_, 2);
lean_inc(v_tail_1283_);
lean_dec_ref_known(v_x_1280_, 3);
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1282_, v_x_1279_, v_key_1281_);
lean_dec(v_value_1282_);
v_x_1279_ = v___x_1284_;
v_x_1280_ = v_tail_1283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1286_, lean_object* v_x_1287_){
_start:
{
if (lean_obj_tag(v_x_1287_) == 0)
{
return v_x_1286_;
}
else
{
lean_object* v_key_1288_; lean_object* v_value_1289_; lean_object* v_tail_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_key_1288_ = lean_ctor_get(v_x_1287_, 0);
lean_inc(v_key_1288_);
v_value_1289_ = lean_ctor_get(v_x_1287_, 1);
lean_inc(v_value_1289_);
v_tail_1290_ = lean_ctor_get(v_x_1287_, 2);
lean_inc(v_tail_1290_);
lean_dec_ref_known(v_x_1287_, 3);
v___x_1291_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1289_, v_x_1286_, v_key_1288_);
lean_dec(v_value_1289_);
v___x_1292_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1291_, v_tail_1290_);
return v___x_1292_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1293_, size_t v_i_1294_, size_t v_stop_1295_, lean_object* v_b_1296_){
_start:
{
uint8_t v___x_1297_; 
v___x_1297_ = lean_usize_dec_eq(v_i_1294_, v_stop_1295_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; 
v___x_1298_ = lean_array_uget_borrowed(v_as_1293_, v_i_1294_);
lean_inc(v___x_1298_);
v___x_1299_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(v_b_1296_, v___x_1298_);
v___x_1300_ = ((size_t)1ULL);
v___x_1301_ = lean_usize_add(v_i_1294_, v___x_1300_);
v_i_1294_ = v___x_1301_;
v_b_1296_ = v___x_1299_;
goto _start;
}
else
{
return v_b_1296_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1293_ = stack[0].m_obj;
size_t v_i_1294_ = stack[1].m_num;
size_t v_stop_1295_ = stack[2].m_num;
lean_object* v_b_1296_ = stack[3].m_obj;
lean_object* v_res_1303_;
v_res_1303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_as_1293_, v_i_1294_, v_stop_1295_, v_b_1296_);
stack->m_obj
 = v_res_1303_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1304_, lean_object* v_i_1305_, lean_object* v_stop_1306_, lean_object* v_b_1307_){
_start:
{
size_t v_i_boxed_1308_; size_t v_stop_boxed_1309_; lean_object* v_res_1310_; 
v_i_boxed_1308_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_stop_boxed_1309_ = lean_unbox_usize(v_stop_1306_);
lean_dec(v_stop_1306_);
v_res_1310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_as_1304_, v_i_boxed_1308_, v_stop_boxed_1309_, v_b_1307_);
lean_dec_ref(v_as_1304_);
return v_res_1310_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1311_, lean_object* v_y_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v___y_1316_; lean_object* v_fst_1317_; lean_object* v_snd_1318_; lean_object* v_size_1322_; lean_object* v_buckets_1323_; lean_object* v_size_1324_; lean_object* v_buckets_1325_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1332_; lean_object* v_buckets_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v_buckets_1346_; lean_object* v_fst_1354_; lean_object* v_buckets_1355_; lean_object* v_snd_1356_; uint8_t v___x_1366_; 
v_size_1322_ = lean_ctor_get(v_y_1312_, 0);
lean_inc(v_size_1322_);
v_buckets_1323_ = lean_ctor_get(v_y_1312_, 1);
v_size_1324_ = lean_ctor_get(v_x_1311_, 0);
lean_inc(v_size_1324_);
v_buckets_1325_ = lean_ctor_get(v_x_1311_, 1);
v___x_1366_ = lean_nat_dec_lt(v_size_1322_, v_size_1324_);
if (v___x_1366_ == 0)
{
lean_inc_ref(v_buckets_1325_);
v_fst_1354_ = v_x_1311_;
v_buckets_1355_ = v_buckets_1325_;
v_snd_1356_ = v_y_1312_;
goto v___jp_1353_;
}
else
{
lean_inc_ref(v_buckets_1323_);
v_fst_1354_ = v_y_1312_;
v_buckets_1355_ = v_buckets_1323_;
v_snd_1356_ = v_x_1311_;
goto v___jp_1353_;
}
v___jp_1315_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1319_, 0, v___y_1316_);
lean_ctor_set(v___x_1319_, 1, v_fst_1317_);
lean_ctor_set(v___x_1319_, 2, v_snd_1318_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v_a_1313_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
v___jp_1326_:
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_nat_dec_lt(v_size_1322_, v_size_1324_);
lean_dec(v_size_1324_);
lean_dec(v_size_1322_);
if (v___x_1330_ == 0)
{
v___y_1316_ = v___y_1327_;
v_fst_1317_ = v___y_1328_;
v_snd_1318_ = v___y_1329_;
goto v___jp_1315_;
}
else
{
v___y_1316_ = v___y_1327_;
v_fst_1317_ = v___y_1329_;
v_snd_1318_ = v___y_1328_;
goto v___jp_1315_;
}
}
v___jp_1331_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = lean_array_get_size(v_buckets_1333_);
v___x_1338_ = lean_nat_dec_lt(v___x_1336_, v___x_1337_);
if (v___x_1338_ == 0)
{
lean_dec_ref(v_buckets_1333_);
v___y_1327_ = v___y_1332_;
v___y_1328_ = v___y_1335_;
v___y_1329_ = v___y_1334_;
goto v___jp_1326_;
}
else
{
size_t v___x_1339_; size_t v___x_1340_; lean_object* v___x_1341_; 
v___x_1339_ = ((size_t)0ULL);
v___x_1340_ = lean_usize_of_nat(v___x_1337_);
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1333_, v___x_1339_, v___x_1340_, v___y_1334_);
lean_dec_ref(v_buckets_1333_);
v___y_1327_ = v___y_1332_;
v___y_1328_ = v___y_1335_;
v___y_1329_ = v___x_1341_;
goto v___jp_1326_;
}
}
v___jp_1342_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_array_get_size(v_buckets_1346_);
v___x_1349_ = lean_nat_dec_lt(v___x_1347_, v___x_1348_);
if (v___x_1349_ == 0)
{
v___y_1332_ = v___y_1345_;
v_buckets_1333_ = v_buckets_1346_;
v___y_1334_ = v___y_1344_;
v___y_1335_ = v___y_1343_;
goto v___jp_1331_;
}
else
{
size_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = ((size_t)0ULL);
v___x_1351_ = lean_usize_of_nat(v___x_1348_);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1346_, v___x_1350_, v___x_1351_, v___y_1343_);
v___y_1332_ = v___y_1345_;
v_buckets_1333_ = v_buckets_1346_;
v___y_1334_ = v___y_1344_;
v___y_1335_ = v___x_1352_;
goto v___jp_1331_;
}
}
v___jp_1353_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1359_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1360_ = lean_array_get_size(v_buckets_1355_);
v___x_1361_ = lean_nat_dec_lt(v___x_1357_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_dec_ref(v_buckets_1355_);
v___y_1343_ = v_fst_1354_;
v___y_1344_ = v_snd_1356_;
v___y_1345_ = v___x_1359_;
v_buckets_1346_ = v___x_1358_;
goto v___jp_1342_;
}
else
{
size_t v___x_1362_; size_t v___x_1363_; lean_object* v___x_1364_; lean_object* v_buckets_1365_; 
v___x_1362_ = ((size_t)0ULL);
v___x_1363_ = lean_usize_of_nat(v___x_1360_);
v___x_1364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1356_, v_buckets_1355_, v___x_1362_, v___x_1363_, v___x_1359_);
lean_dec_ref(v_buckets_1355_);
v_buckets_1365_ = lean_ctor_get(v___x_1364_, 1);
lean_inc_ref(v_buckets_1365_);
v___y_1343_ = v_fst_1354_;
v___y_1344_ = v_snd_1356_;
v___y_1345_ = v___x_1364_;
v_buckets_1346_ = v_buckets_1365_;
goto v___jp_1342_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1311_ = stack[0].m_obj;
lean_object* v_y_1312_ = stack[1].m_obj;
lean_object* v_a_1313_ = stack[2].m_obj;
lean_object* v_res_1367_;
v_res_1367_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1311_, v_y_1312_, v_a_1313_);
stack->m_obj
 = v_res_1367_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1368_, lean_object* v_y_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1368_, v_y_1369_, v_a_1370_);
return v_res_1372_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object* v_x_1373_, lean_object* v_y_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1373_, v_y_1374_, v_a_1375_);
return v___x_1383_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1373_ = stack[0].m_obj;
lean_object* v_y_1374_ = stack[1].m_obj;
lean_object* v_a_1375_ = stack[2].m_obj;
lean_object* v_a_1376_ = stack[3].m_obj;
lean_object* v_a_1377_ = stack[4].m_obj;
lean_object* v_a_1378_ = stack[5].m_obj;
lean_object* v_a_1379_ = stack[6].m_obj;
lean_object* v_a_1380_ = stack[7].m_obj;
lean_object* v_a_1381_ = stack[8].m_obj;
lean_object* v_res_1384_;
v_res_1384_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(v_x_1373_, v_y_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_);
stack->m_obj
 = v_res_1384_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1385_, lean_object* v_y_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(v_x_1385_, v_y_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1396_, lean_object* v_m_1397_, lean_object* v_a_1398_, lean_object* v_b_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1397_, v_a_1398_, v_b_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1401_, lean_object* v_m_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1402_, v_a_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1405_, lean_object* v_m_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1405_, v_m_1406_, v_a_1407_);
lean_dec(v_a_1407_);
lean_dec_ref(v_m_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1409_, lean_object* v_a_1410_, lean_object* v_b_1411_, lean_object* v_x_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1410_, v_b_1411_, v_x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1414_, lean_object* v_a_1415_, lean_object* v_x_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1415_, v_x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1418_, lean_object* v_a_1419_, lean_object* v_x_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1418_, v_a_1419_, v_x_1420_);
lean_dec(v_x_1420_);
lean_dec(v_a_1419_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
if (lean_obj_tag(v_x_1423_) == 0)
{
return v_x_1422_;
}
else
{
lean_object* v_key_1424_; lean_object* v_value_1425_; lean_object* v_tail_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_key_1424_ = lean_ctor_get(v_x_1423_, 0);
v_value_1425_ = lean_ctor_get(v_x_1423_, 1);
v_tail_1426_ = lean_ctor_get(v_x_1423_, 2);
lean_inc(v_value_1425_);
lean_inc(v_key_1424_);
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_key_1424_);
lean_ctor_set(v___x_1427_, 1, v_value_1425_);
v___x_1428_ = lean_array_push(v_x_1422_, v___x_1427_);
v_x_1422_ = v___x_1428_;
v_x_1423_ = v_tail_1426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1430_, lean_object* v_x_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1430_, v_x_1431_);
lean_dec(v_x_1431_);
return v_res_1432_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1433_, size_t v_i_1434_, size_t v_stop_1435_, lean_object* v_b_1436_){
_start:
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_usize_dec_eq(v_i_1434_, v_stop_1435_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; 
v___x_1438_ = lean_array_uget_borrowed(v_as_1433_, v_i_1434_);
v___x_1439_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1436_, v___x_1438_);
v___x_1440_ = ((size_t)1ULL);
v___x_1441_ = lean_usize_add(v_i_1434_, v___x_1440_);
v_i_1434_ = v___x_1441_;
v_b_1436_ = v___x_1439_;
goto _start;
}
else
{
return v_b_1436_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1433_ = stack[0].m_obj;
size_t v_i_1434_ = stack[1].m_num;
size_t v_stop_1435_ = stack[2].m_num;
lean_object* v_b_1436_ = stack[3].m_obj;
lean_object* v_res_1443_;
v_res_1443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1433_, v_i_1434_, v_stop_1435_, v_b_1436_);
stack->m_obj
 = v_res_1443_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1444_, lean_object* v_i_1445_, lean_object* v_stop_1446_, lean_object* v_b_1447_){
_start:
{
size_t v_i_boxed_1448_; size_t v_stop_boxed_1449_; lean_object* v_res_1450_; 
v_i_boxed_1448_ = lean_unbox_usize(v_i_1445_);
lean_dec(v_i_1445_);
v_stop_boxed_1449_ = lean_unbox_usize(v_stop_1446_);
lean_dec(v_stop_1446_);
v_res_1450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1444_, v_i_boxed_1448_, v_stop_boxed_1449_, v_b_1447_);
lean_dec_ref(v_as_1444_);
return v_res_1450_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1451_, lean_object* v___x_1452_, lean_object* v_op_1453_, lean_object* v_a_1454_, lean_object* v_b_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___y_1459_; uint8_t v___x_1463_; 
v___x_1463_ = lean_nat_dec_lt(v_a_1454_, v_upperBound_1451_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_dec(v_a_1454_);
lean_dec_ref(v_op_1453_);
lean_dec_ref(v___x_1452_);
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v_b_1455_);
lean_ctor_set(v___x_1464_, 1, v___y_1456_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
else
{
if (lean_obj_tag(v_b_1455_) == 0)
{
lean_object* v___x_1466_; 
lean_inc_ref(v___x_1452_);
v___x_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1452_);
v___y_1459_ = v___x_1466_;
goto v___jp_1458_;
}
else
{
lean_object* v_val_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1476_; 
v_val_1467_ = lean_ctor_get(v_b_1455_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_b_1455_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1469_ = v_b_1455_;
v_isShared_1470_ = v_isSharedCheck_1476_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_val_1467_);
lean_dec(v_b_1455_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1476_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_inc_ref(v_op_1453_);
v___x_1471_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_1453_);
lean_inc_ref(v___x_1452_);
v___x_1472_ = l_Lean_mkAppB(v___x_1471_, v_val_1467_, v___x_1452_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1472_);
v___x_1474_ = v___x_1469_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
v___y_1459_ = v___x_1474_;
goto v___jp_1458_;
}
}
}
}
v___jp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_unsigned_to_nat(1u);
v___x_1461_ = lean_nat_add(v_a_1454_, v___x_1460_);
lean_dec(v_a_1454_);
v_a_1454_ = v___x_1461_;
v_b_1455_ = v___y_1459_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1451_ = stack[0].m_obj;
lean_object* v___x_1452_ = stack[1].m_obj;
lean_object* v_op_1453_ = stack[2].m_obj;
lean_object* v_a_1454_ = stack[3].m_obj;
lean_object* v_b_1455_ = stack[4].m_obj;
lean_object* v___y_1456_ = stack[5].m_obj;
lean_object* v_res_1477_;
v_res_1477_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1451_, v___x_1452_, v_op_1453_, v_a_1454_, v_b_1455_, v___y_1456_);
stack->m_obj
 = v_res_1477_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1478_, lean_object* v___x_1479_, lean_object* v_op_1480_, lean_object* v_a_1481_, lean_object* v_b_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1478_, v___x_1479_, v_op_1480_, v_a_1481_, v_b_1482_, v___y_1483_);
lean_dec(v_upperBound_1478_);
return v_res_1485_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1486_, lean_object* v_as_1487_, size_t v_sz_1488_, size_t v_i_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v___x_1499_; 
v___x_1499_ = lean_usize_dec_lt(v_i_1489_, v_sz_1488_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec_ref(v_op_1486_);
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_b_1490_);
lean_ctor_set(v___x_1500_, 1, v___y_1491_);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
else
{
lean_object* v_a_1502_; lean_object* v_fst_1503_; lean_object* v_snd_1504_; lean_object* v_varToExpr_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_a_1502_ = lean_array_uget_borrowed(v_as_1487_, v_i_1489_);
v_fst_1503_ = lean_ctor_get(v_a_1502_, 0);
v_snd_1504_ = lean_ctor_get(v_a_1502_, 1);
v_varToExpr_1505_ = lean_ctor_get(v___y_1491_, 2);
v___x_1506_ = l_Lean_instInhabitedExpr;
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = lean_array_get(v___x_1506_, v_varToExpr_1505_, v_fst_1503_);
lean_inc_ref(v_op_1486_);
v___x_1509_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1504_, v___x_1508_, v_op_1486_, v___x_1507_, v_b_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v_fst_1511_; lean_object* v_snd_1512_; size_t v___x_1513_; size_t v___x_1514_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v_fst_1511_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_fst_1511_);
v_snd_1512_ = lean_ctor_get(v_a_1510_, 1);
lean_inc(v_snd_1512_);
lean_dec(v_a_1510_);
v___x_1513_ = ((size_t)1ULL);
v___x_1514_ = lean_usize_add(v_i_1489_, v___x_1513_);
v_i_1489_ = v___x_1514_;
v_b_1490_ = v_fst_1511_;
v___y_1491_ = v_snd_1512_;
goto _start;
}
else
{
lean_dec_ref(v_op_1486_);
return v___x_1509_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_1486_ = stack[0].m_obj;
lean_object* v_as_1487_ = stack[1].m_obj;
size_t v_sz_1488_ = stack[2].m_num;
size_t v_i_1489_ = stack[3].m_num;
lean_object* v_b_1490_ = stack[4].m_obj;
lean_object* v___y_1491_ = stack[5].m_obj;
lean_object* v___y_1492_ = stack[6].m_obj;
lean_object* v___y_1493_ = stack[7].m_obj;
lean_object* v___y_1494_ = stack[8].m_obj;
lean_object* v___y_1495_ = stack[9].m_obj;
lean_object* v___y_1496_ = stack[10].m_obj;
lean_object* v___y_1497_ = stack[11].m_obj;
lean_object* v_res_1516_;
v_res_1516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1486_, v_as_1487_, v_sz_1488_, v_i_1489_, v_b_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
stack->m_obj
 = v_res_1516_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1517_, lean_object* v_as_1518_, lean_object* v_sz_1519_, lean_object* v_i_1520_, lean_object* v_b_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
size_t v_sz_boxed_1530_; size_t v_i_boxed_1531_; lean_object* v_res_1532_; 
v_sz_boxed_1530_ = lean_unbox_usize(v_sz_1519_);
lean_dec(v_sz_1519_);
v_i_boxed_1531_ = lean_unbox_usize(v_i_1520_);
lean_dec(v_i_1520_);
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1517_, v_as_1518_, v_sz_boxed_1530_, v_i_boxed_1531_, v_b_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec_ref(v_as_1518_);
return v_res_1532_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1533_, lean_object* v_x2_1534_){
_start:
{
lean_object* v_fst_1535_; lean_object* v_fst_1536_; uint8_t v___x_1537_; 
v_fst_1535_ = lean_ctor_get(v_x1_1533_, 0);
v_fst_1536_ = lean_ctor_get(v_x2_1534_, 0);
v___x_1537_ = lean_nat_dec_lt(v_fst_1535_, v_fst_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_1533_ = stack[0].m_obj;
lean_object* v_x2_1534_ = stack[1].m_obj;
uint8_t v_res_1538_;
v_res_1538_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1533_, v_x2_1534_);
stack->m_num = v_res_1538_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1539_, lean_object* v_x2_1540_){
_start:
{
uint8_t v_res_1541_; lean_object* v_r_1542_; 
v_res_1541_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1539_, v_x2_1540_);
lean_dec_ref(v_x2_1540_);
lean_dec_ref(v_x1_1539_);
v_r_1542_ = lean_box(v_res_1541_);
return v_r_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object* v_hi_1543_, lean_object* v_pivot_1544_, lean_object* v_as_1545_, lean_object* v_i_1546_, lean_object* v_k_1547_){
_start:
{
uint8_t v___x_1548_; 
v___x_1548_ = lean_nat_dec_lt(v_k_1547_, v_hi_1543_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec(v_k_1547_);
v___x_1549_ = lean_array_fswap(v_as_1545_, v_i_1546_, v_hi_1543_);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_i_1546_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
return v___x_1550_;
}
else
{
lean_object* v___x_1551_; lean_object* v_fst_1552_; lean_object* v_fst_1553_; uint8_t v___x_1554_; 
v___x_1551_ = lean_array_fget_borrowed(v_as_1545_, v_k_1547_);
v_fst_1552_ = lean_ctor_get(v___x_1551_, 0);
v_fst_1553_ = lean_ctor_get(v_pivot_1544_, 0);
v___x_1554_ = lean_nat_dec_lt(v_fst_1552_, v_fst_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_nat_add(v_k_1547_, v___x_1555_);
lean_dec(v_k_1547_);
v_k_1547_ = v___x_1556_;
goto _start;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1558_ = lean_array_fswap(v_as_1545_, v_i_1546_, v_k_1547_);
v___x_1559_ = lean_unsigned_to_nat(1u);
v___x_1560_ = lean_nat_add(v_i_1546_, v___x_1559_);
lean_dec(v_i_1546_);
v___x_1561_ = lean_nat_add(v_k_1547_, v___x_1559_);
lean_dec(v_k_1547_);
v_as_1545_ = v___x_1558_;
v_i_1546_ = v___x_1560_;
v_k_1547_ = v___x_1561_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object* v_hi_1563_, lean_object* v_pivot_1564_, lean_object* v_as_1565_, lean_object* v_i_1566_, lean_object* v_k_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1563_, v_pivot_1564_, v_as_1565_, v_i_1566_, v_k_1567_);
lean_dec_ref(v_pivot_1564_);
lean_dec(v_hi_1563_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_n_1569_, lean_object* v_as_1570_, lean_object* v_lo_1571_, lean_object* v_hi_1572_){
_start:
{
lean_object* v___y_1574_; uint8_t v___x_1584_; 
v___x_1584_ = lean_nat_dec_lt(v_lo_1571_, v_hi_1572_);
if (v___x_1584_ == 0)
{
lean_dec(v_lo_1571_);
return v_as_1570_;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v_mid_1587_; lean_object* v___y_1589_; lean_object* v___y_1595_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1585_ = lean_nat_add(v_lo_1571_, v_hi_1572_);
v___x_1586_ = lean_unsigned_to_nat(1u);
v_mid_1587_ = lean_nat_shiftr(v___x_1585_, v___x_1586_);
lean_dec(v___x_1585_);
v___x_1600_ = lean_array_fget_borrowed(v_as_1570_, v_mid_1587_);
v___x_1601_ = lean_array_fget_borrowed(v_as_1570_, v_lo_1571_);
v___x_1602_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1600_, v___x_1601_);
if (v___x_1602_ == 0)
{
v___y_1595_ = v_as_1570_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_array_fswap(v_as_1570_, v_lo_1571_, v_mid_1587_);
v___y_1595_ = v___x_1603_;
goto v___jp_1594_;
}
v___jp_1588_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1590_ = lean_array_fget_borrowed(v___y_1589_, v_mid_1587_);
v___x_1591_ = lean_array_fget_borrowed(v___y_1589_, v_hi_1572_);
v___x_1592_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1590_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_dec(v_mid_1587_);
v___y_1574_ = v___y_1589_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_array_fswap(v___y_1589_, v_mid_1587_, v_hi_1572_);
lean_dec(v_mid_1587_);
v___y_1574_ = v___x_1593_;
goto v___jp_1573_;
}
}
v___jp_1594_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1596_ = lean_array_fget_borrowed(v___y_1595_, v_hi_1572_);
v___x_1597_ = lean_array_fget_borrowed(v___y_1595_, v_lo_1571_);
v___x_1598_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1596_, v___x_1597_);
if (v___x_1598_ == 0)
{
v___y_1589_ = v___y_1595_;
goto v___jp_1588_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_array_fswap(v___y_1595_, v_lo_1571_, v_hi_1572_);
v___y_1589_ = v___x_1599_;
goto v___jp_1588_;
}
}
}
v___jp_1573_:
{
lean_object* v_pivot_1575_; lean_object* v___x_1576_; lean_object* v_fst_1577_; lean_object* v_snd_1578_; uint8_t v___x_1579_; 
v_pivot_1575_ = lean_array_fget(v___y_1574_, v_hi_1572_);
lean_inc_n(v_lo_1571_, 2);
v___x_1576_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1572_, v_pivot_1575_, v___y_1574_, v_lo_1571_, v_lo_1571_);
lean_dec(v_pivot_1575_);
v_fst_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_fst_1577_);
v_snd_1578_ = lean_ctor_get(v___x_1576_, 1);
lean_inc(v_snd_1578_);
lean_dec_ref(v___x_1576_);
v___x_1579_ = lean_nat_dec_le(v_hi_1572_, v_fst_1577_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1569_, v_snd_1578_, v_lo_1571_, v_fst_1577_);
v___x_1581_ = lean_unsigned_to_nat(1u);
v___x_1582_ = lean_nat_add(v_fst_1577_, v___x_1581_);
lean_dec(v_fst_1577_);
v_as_1570_ = v___x_1580_;
v_lo_1571_ = v___x_1582_;
goto _start;
}
else
{
lean_dec(v_fst_1577_);
lean_dec(v_lo_1571_);
return v_snd_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_n_1604_, lean_object* v_as_1605_, lean_object* v_lo_1606_, lean_object* v_hi_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1604_, v_as_1605_, v_lo_1606_, v_hi_1607_);
lean_dec(v_hi_1607_);
lean_dec(v_n_1604_);
return v_res_1608_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1609_, lean_object* v_op_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v___y_1620_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1638_; lean_object* v_size_1645_; lean_object* v_buckets_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v_size_1645_ = lean_ctor_get(v_coeff_1609_, 0);
v_buckets_1646_ = lean_ctor_get(v_coeff_1609_, 1);
v___x_1647_ = lean_mk_empty_array_with_capacity(v_size_1645_);
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = lean_array_get_size(v_buckets_1646_);
v___x_1650_ = lean_nat_dec_lt(v___x_1648_, v___x_1649_);
if (v___x_1650_ == 0)
{
v___y_1638_ = v___x_1647_;
goto v___jp_1637_;
}
else
{
size_t v___x_1651_; size_t v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = ((size_t)0ULL);
v___x_1652_ = lean_usize_of_nat(v___x_1649_);
v___x_1653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1646_, v___x_1651_, v___x_1652_, v___x_1647_);
v___y_1638_ = v___x_1653_;
goto v___jp_1637_;
}
v___jp_1619_:
{
lean_object* v_acc_1621_; size_t v_sz_1622_; size_t v___x_1623_; lean_object* v___x_1624_; 
v_acc_1621_ = lean_box(0);
v_sz_1622_ = lean_array_size(v___y_1620_);
v___x_1623_ = ((size_t)0ULL);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1610_, v___y_1620_, v_sz_1622_, v___x_1623_, v_acc_1621_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
lean_dec_ref(v___y_1620_);
return v___x_1624_;
}
v___jp_1625_:
{
lean_object* v___x_1630_; 
v___x_1630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1628_, v___y_1627_, v___y_1626_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec(v___y_1628_);
v___y_1620_ = v___x_1630_;
goto v___jp_1619_;
}
v___jp_1631_:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_nat_dec_le(v___y_1635_, v___y_1632_);
if (v___x_1636_ == 0)
{
lean_dec(v___y_1632_);
lean_inc(v___y_1635_);
v___y_1626_ = v___y_1635_;
v___y_1627_ = v___y_1633_;
v___y_1628_ = v___y_1634_;
v___y_1629_ = v___y_1635_;
goto v___jp_1625_;
}
else
{
v___y_1626_ = v___y_1635_;
v___y_1627_ = v___y_1633_;
v___y_1628_ = v___y_1634_;
v___y_1629_ = v___y_1632_;
goto v___jp_1625_;
}
}
v___jp_1637_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1639_ = lean_array_get_size(v___y_1638_);
v___x_1640_ = lean_unsigned_to_nat(0u);
v___x_1641_ = lean_nat_dec_eq(v___x_1639_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1642_ = lean_unsigned_to_nat(1u);
v___x_1643_ = lean_nat_sub(v___x_1639_, v___x_1642_);
v___x_1644_ = lean_nat_dec_le(v___x_1640_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_inc(v___x_1643_);
v___y_1632_ = v___x_1643_;
v___y_1633_ = v___y_1638_;
v___y_1634_ = v___x_1639_;
v___y_1635_ = v___x_1643_;
goto v___jp_1631_;
}
else
{
v___y_1632_ = v___x_1643_;
v___y_1633_ = v___y_1638_;
v___y_1634_ = v___x_1639_;
v___y_1635_ = v___x_1640_;
goto v___jp_1631_;
}
}
else
{
v___y_1620_ = v___y_1638_;
goto v___jp_1619_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_coeff_1609_ = stack[0].m_obj;
lean_object* v_op_1610_ = stack[1].m_obj;
lean_object* v_a_1611_ = stack[2].m_obj;
lean_object* v_a_1612_ = stack[3].m_obj;
lean_object* v_a_1613_ = stack[4].m_obj;
lean_object* v_a_1614_ = stack[5].m_obj;
lean_object* v_a_1615_ = stack[6].m_obj;
lean_object* v_a_1616_ = stack[7].m_obj;
lean_object* v_a_1617_ = stack[8].m_obj;
lean_object* v_res_1654_;
v_res_1654_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_coeff_1609_, v_op_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
stack->m_obj
 = v_res_1654_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1655_, lean_object* v_op_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_coeff_1655_, v_op_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec_ref(v_coeff_1655_);
return v_res_1665_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1666_, lean_object* v___x_1667_, lean_object* v_op_1668_, lean_object* v_inst_1669_, lean_object* v_R_1670_, lean_object* v_a_1671_, lean_object* v_b_1672_, lean_object* v_c_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1666_, v___x_1667_, v_op_1668_, v_a_1671_, v_b_1672_, v___y_1674_);
return v___x_1682_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1666_ = stack[0].m_obj;
lean_object* v___x_1667_ = stack[1].m_obj;
lean_object* v_op_1668_ = stack[2].m_obj;
lean_object* v_a_1671_ = stack[5].m_obj;
lean_object* v_b_1672_ = stack[6].m_obj;
lean_object* v___y_1674_ = stack[8].m_obj;
lean_object* v___y_1675_ = stack[9].m_obj;
lean_object* v___y_1676_ = stack[10].m_obj;
lean_object* v___y_1677_ = stack[11].m_obj;
lean_object* v___y_1678_ = stack[12].m_obj;
lean_object* v___y_1679_ = stack[13].m_obj;
lean_object* v___y_1680_ = stack[14].m_obj;
lean_object* v_res_1683_;
v_res_1683_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1666_, v___x_1667_, v_op_1668_, lean_box(0), lean_box(0), v_a_1671_, v_b_1672_, lean_box(0), v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
stack->m_obj
 = v_res_1683_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1684_, lean_object* v___x_1685_, lean_object* v_op_1686_, lean_object* v_inst_1687_, lean_object* v_R_1688_, lean_object* v_a_1689_, lean_object* v_b_1690_, lean_object* v_c_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1684_, v___x_1685_, v_op_1686_, v_inst_1687_, v_R_1688_, v_a_1689_, v_b_1690_, v_c_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v_upperBound_1684_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1701_, lean_object* v_as_1702_, lean_object* v_lo_1703_, lean_object* v_hi_1704_, lean_object* v_w_1705_, lean_object* v_hlo_1706_, lean_object* v_hhi_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1701_, v_as_1702_, v_lo_1703_, v_hi_1704_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1709_, lean_object* v_as_1710_, lean_object* v_lo_1711_, lean_object* v_hi_1712_, lean_object* v_w_1713_, lean_object* v_hlo_1714_, lean_object* v_hhi_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1709_, v_as_1710_, v_lo_1711_, v_hi_1712_, v_w_1713_, v_hlo_1714_, v_hhi_1715_);
lean_dec(v_hi_1712_);
lean_dec(v_n_1709_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object* v_n_1717_, lean_object* v_lo_1718_, lean_object* v_hi_1719_, lean_object* v_hhi_1720_, lean_object* v_pivot_1721_, lean_object* v_as_1722_, lean_object* v_i_1723_, lean_object* v_k_1724_, lean_object* v_ilo_1725_, lean_object* v_ik_1726_, lean_object* v_w_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1719_, v_pivot_1721_, v_as_1722_, v_i_1723_, v_k_1724_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object* v_n_1729_, lean_object* v_lo_1730_, lean_object* v_hi_1731_, lean_object* v_hhi_1732_, lean_object* v_pivot_1733_, lean_object* v_as_1734_, lean_object* v_i_1735_, lean_object* v_k_1736_, lean_object* v_ilo_1737_, lean_object* v_ik_1738_, lean_object* v_w_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_n_1729_, v_lo_1730_, v_hi_1731_, v_hhi_1732_, v_pivot_1733_, v_as_1734_, v_i_1735_, v_k_1736_, v_ilo_1737_, v_ik_1738_, v_w_1739_);
lean_dec_ref(v_pivot_1733_);
lean_dec(v_hi_1731_);
lean_dec(v_lo_1730_);
lean_dec(v_n_1729_);
return v_res_1740_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1741_, lean_object* v___y_1742_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = l_Lean_Expr_hasMVar(v_e_1741_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_e_1741_);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; lean_object* v_mctx_1747_; lean_object* v___x_1748_; lean_object* v_fst_1749_; lean_object* v_snd_1750_; lean_object* v___x_1751_; lean_object* v_cache_1752_; lean_object* v_zetaDeltaFVarIds_1753_; lean_object* v_postponed_1754_; lean_object* v_diag_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1764_; 
v___x_1746_ = lean_st_ref_get(v___y_1742_);
v_mctx_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc_ref(v_mctx_1747_);
lean_dec(v___x_1746_);
v___x_1748_ = l_Lean_instantiateMVarsCore(v_mctx_1747_, v_e_1741_);
v_fst_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_fst_1749_);
v_snd_1750_ = lean_ctor_get(v___x_1748_, 1);
lean_inc(v_snd_1750_);
lean_dec_ref(v___x_1748_);
v___x_1751_ = lean_st_ref_take(v___y_1742_);
v_cache_1752_ = lean_ctor_get(v___x_1751_, 1);
v_zetaDeltaFVarIds_1753_ = lean_ctor_get(v___x_1751_, 2);
v_postponed_1754_ = lean_ctor_get(v___x_1751_, 3);
v_diag_1755_ = lean_ctor_get(v___x_1751_, 4);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1764_ == 0)
{
lean_object* v_unused_1765_; 
v_unused_1765_ = lean_ctor_get(v___x_1751_, 0);
lean_dec(v_unused_1765_);
v___x_1757_ = v___x_1751_;
v_isShared_1758_ = v_isSharedCheck_1764_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_diag_1755_);
lean_inc(v_postponed_1754_);
lean_inc(v_zetaDeltaFVarIds_1753_);
lean_inc(v_cache_1752_);
lean_dec(v___x_1751_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1764_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v_snd_1750_);
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_snd_1750_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_cache_1752_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_zetaDeltaFVarIds_1753_);
lean_ctor_set(v_reuseFailAlloc_1763_, 3, v_postponed_1754_);
lean_ctor_set(v_reuseFailAlloc_1763_, 4, v_diag_1755_);
v___x_1760_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_st_ref_put(v___y_1742_, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v_fst_1749_);
return v___x_1762_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1741_ = stack[0].m_obj;
lean_object* v___y_1742_ = stack[1].m_obj;
lean_object* v_res_1766_;
v_res_1766_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1741_, v___y_1742_);
stack->m_obj
 = v_res_1766_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1767_, v___y_1768_);
lean_dec(v___y_1768_);
return v_res_1770_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1771_, v___y_1773_);
return v___x_1777_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1771_ = stack[0].m_obj;
lean_object* v___y_1772_ = stack[1].m_obj;
lean_object* v___y_1773_ = stack[2].m_obj;
lean_object* v___y_1774_ = stack[3].m_obj;
lean_object* v___y_1775_ = stack[4].m_obj;
lean_object* v_res_1778_;
v_res_1778_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(v_e_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
stack->m_obj
 = v_res_1778_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(v_e_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
return v_res_1785_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object* v_x_1786_, lean_object* v_y_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_Meta_mkEq(v_x_1786_, v_y_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1816_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1816_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1816_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set_tag(v___x_1796_, 1);
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
uint8_t v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = 0;
v___x_1801_ = lean_box(0);
v___x_1802_ = l_Lean_Meta_mkFreshExprMVar(v___x_1799_, v___x_1800_, v___x_1801_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v___x_1804_ = l_Lean_Expr_mvarId_x21(v_a_1803_);
v___x_1805_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1804_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v___x_1806_; 
lean_dec_ref_known(v___x_1805_, 1);
v___x_1806_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1803_, v_a_1789_);
return v___x_1806_;
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec(v_a_1803_);
v_a_1807_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1805_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1805_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
else
{
return v___x_1802_;
}
}
}
}
else
{
return v___x_1793_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1786_ = stack[0].m_obj;
lean_object* v_y_1787_ = stack[1].m_obj;
lean_object* v_a_1788_ = stack[2].m_obj;
lean_object* v_a_1789_ = stack[3].m_obj;
lean_object* v_a_1790_ = stack[4].m_obj;
lean_object* v_a_1791_ = stack[5].m_obj;
lean_object* v_res_1817_;
v_res_1817_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v_x_1786_, v_y_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
stack->m_obj
 = v_res_1817_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1818_, lean_object* v_y_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v_x_1818_, v_y_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
return v_res_1825_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_unsigned_to_nat(32u);
v___x_1827_ = lean_mk_empty_array_with_capacity(v___x_1826_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1829_ = ((size_t)5ULL);
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = lean_unsigned_to_nat(32u);
v___x_1832_ = lean_mk_empty_array_with_capacity(v___x_1831_);
v___x_1833_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1834_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v___x_1832_);
lean_ctor_set(v___x_1834_, 2, v___x_1830_);
lean_ctor_set(v___x_1834_, 3, v___x_1830_);
lean_ctor_set_usize(v___x_1834_, 4, v___x_1829_);
return v___x_1834_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; lean_object* v_traceState_1838_; lean_object* v_traces_1839_; lean_object* v___x_1840_; lean_object* v_traceState_1841_; lean_object* v_env_1842_; lean_object* v_nextMacroScope_1843_; lean_object* v_ngen_1844_; lean_object* v_auxDeclNGen_1845_; lean_object* v_cache_1846_; lean_object* v_recordedDeps_1847_; lean_object* v_messages_1848_; lean_object* v_infoState_1849_; lean_object* v_snapshotTasks_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1869_; 
v___x_1837_ = lean_st_ref_get(v___y_1835_);
v_traceState_1838_ = lean_ctor_get(v___x_1837_, 4);
lean_inc_ref(v_traceState_1838_);
lean_dec(v___x_1837_);
v_traces_1839_ = lean_ctor_get(v_traceState_1838_, 0);
lean_inc_ref(v_traces_1839_);
lean_dec_ref(v_traceState_1838_);
v___x_1840_ = lean_st_ref_take(v___y_1835_);
v_traceState_1841_ = lean_ctor_get(v___x_1840_, 4);
v_env_1842_ = lean_ctor_get(v___x_1840_, 0);
v_nextMacroScope_1843_ = lean_ctor_get(v___x_1840_, 1);
v_ngen_1844_ = lean_ctor_get(v___x_1840_, 2);
v_auxDeclNGen_1845_ = lean_ctor_get(v___x_1840_, 3);
v_cache_1846_ = lean_ctor_get(v___x_1840_, 5);
v_recordedDeps_1847_ = lean_ctor_get(v___x_1840_, 6);
v_messages_1848_ = lean_ctor_get(v___x_1840_, 7);
v_infoState_1849_ = lean_ctor_get(v___x_1840_, 8);
v_snapshotTasks_1850_ = lean_ctor_get(v___x_1840_, 9);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1852_ = v___x_1840_;
v_isShared_1853_ = v_isSharedCheck_1869_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_snapshotTasks_1850_);
lean_inc(v_infoState_1849_);
lean_inc(v_messages_1848_);
lean_inc(v_recordedDeps_1847_);
lean_inc(v_cache_1846_);
lean_inc(v_traceState_1841_);
lean_inc(v_auxDeclNGen_1845_);
lean_inc(v_ngen_1844_);
lean_inc(v_nextMacroScope_1843_);
lean_inc(v_env_1842_);
lean_dec(v___x_1840_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1869_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
uint64_t v_tid_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1867_; 
v_tid_1854_ = lean_ctor_get_uint64(v_traceState_1841_, sizeof(void*)*1);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_traceState_1841_);
if (v_isSharedCheck_1867_ == 0)
{
lean_object* v_unused_1868_; 
v_unused_1868_ = lean_ctor_get(v_traceState_1841_, 0);
lean_dec(v_unused_1868_);
v___x_1856_ = v_traceState_1841_;
v_isShared_1857_ = v_isSharedCheck_1867_;
goto v_resetjp_1855_;
}
else
{
lean_dec(v_traceState_1841_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1867_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1858_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1858_);
v___x_1860_ = v___x_1856_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1858_);
lean_ctor_set_uint64(v_reuseFailAlloc_1866_, sizeof(void*)*1, v_tid_1854_);
v___x_1860_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1862_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 4, v___x_1860_);
v___x_1862_ = v___x_1852_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_env_1842_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_nextMacroScope_1843_);
lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_ngen_1844_);
lean_ctor_set(v_reuseFailAlloc_1865_, 3, v_auxDeclNGen_1845_);
lean_ctor_set(v_reuseFailAlloc_1865_, 4, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1865_, 5, v_cache_1846_);
lean_ctor_set(v_reuseFailAlloc_1865_, 6, v_recordedDeps_1847_);
lean_ctor_set(v_reuseFailAlloc_1865_, 7, v_messages_1848_);
lean_ctor_set(v_reuseFailAlloc_1865_, 8, v_infoState_1849_);
lean_ctor_set(v_reuseFailAlloc_1865_, 9, v_snapshotTasks_1850_);
v___x_1862_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_st_ref_put(v___y_1835_, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_traces_1839_);
return v___x_1864_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1835_ = stack[0].m_obj;
lean_object* v_res_1870_;
v_res_1870_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1835_);
stack->m_obj
 = v_res_1870_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1871_);
lean_dec(v___y_1871_);
return v_res_1873_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1882_);
return v___x_1884_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1874_ = stack[0].m_obj;
lean_object* v___y_1875_ = stack[1].m_obj;
lean_object* v___y_1876_ = stack[2].m_obj;
lean_object* v___y_1877_ = stack[3].m_obj;
lean_object* v___y_1878_ = stack[4].m_obj;
lean_object* v___y_1879_ = stack[5].m_obj;
lean_object* v___y_1880_ = stack[6].m_obj;
lean_object* v___y_1881_ = stack[7].m_obj;
lean_object* v___y_1882_ = stack[8].m_obj;
lean_object* v_res_1885_;
v_res_1885_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
stack->m_obj
 = v_res_1885_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
return v_res_1896_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1897_, lean_object* v_opt_1898_){
_start:
{
lean_object* v_name_1899_; lean_object* v_defValue_1900_; lean_object* v_map_1901_; lean_object* v___x_1902_; 
v_name_1899_ = lean_ctor_get(v_opt_1898_, 0);
v_defValue_1900_ = lean_ctor_get(v_opt_1898_, 1);
v_map_1901_ = lean_ctor_get(v_opts_1897_, 0);
v___x_1902_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1901_, v_name_1899_);
if (lean_obj_tag(v___x_1902_) == 0)
{
uint8_t v___x_1903_; 
v___x_1903_ = lean_unbox(v_defValue_1900_);
return v___x_1903_;
}
else
{
lean_object* v_val_1904_; 
v_val_1904_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_val_1904_);
lean_dec_ref_known(v___x_1902_, 1);
if (lean_obj_tag(v_val_1904_) == 1)
{
uint8_t v_v_1905_; 
v_v_1905_ = lean_ctor_get_uint8(v_val_1904_, 0);
lean_dec_ref_known(v_val_1904_, 0);
return v_v_1905_;
}
else
{
uint8_t v___x_1906_; 
lean_dec(v_val_1904_);
v___x_1906_ = lean_unbox(v_defValue_1900_);
return v___x_1906_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1897_ = stack[0].m_obj;
lean_object* v_opt_1898_ = stack[1].m_obj;
uint8_t v_res_1907_;
v_res_1907_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_1897_, v_opt_1898_);
stack->m_num = v_res_1907_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1908_, lean_object* v_opt_1909_){
_start:
{
uint8_t v_res_1910_; lean_object* v_r_1911_; 
v_res_1910_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_1908_, v_opt_1909_);
lean_dec_ref(v_opt_1909_);
lean_dec_ref(v_opts_1908_);
v_r_1911_ = lean_box(v_res_1910_);
return v_r_1911_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1912_, lean_object* v_____do__lift_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_toCold_1924_; lean_object* v_options_1925_; uint8_t v_hasTrace_1926_; 
v_toCold_1924_ = lean_ctor_get(v___y_1921_, 0);
v_options_1925_ = lean_ctor_get(v_toCold_1924_, 2);
v_hasTrace_1926_ = lean_ctor_get_uint8(v_options_1925_, sizeof(void*)*1);
if (v_hasTrace_1926_ == 0)
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_dec(v_cls_1912_);
v___x_1927_ = lean_box(v_hasTrace_1926_);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1930_ = l_Lean_Name_append(v___x_1929_, v_cls_1912_);
v___x_1931_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1913_, v_options_1925_, v___x_1930_);
lean_dec(v___x_1930_);
v___x_1932_ = lean_box(v___x_1931_);
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
return v___x_1933_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1912_ = stack[0].m_obj;
lean_object* v_____do__lift_1913_ = stack[1].m_obj;
lean_object* v___y_1914_ = stack[2].m_obj;
lean_object* v___y_1915_ = stack[3].m_obj;
lean_object* v___y_1916_ = stack[4].m_obj;
lean_object* v___y_1917_ = stack[5].m_obj;
lean_object* v___y_1918_ = stack[6].m_obj;
lean_object* v___y_1919_ = stack[7].m_obj;
lean_object* v___y_1920_ = stack[8].m_obj;
lean_object* v___y_1921_ = stack[9].m_obj;
lean_object* v___y_1922_ = stack[10].m_obj;
lean_object* v_res_1934_;
v_res_1934_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_1912_, v_____do__lift_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
stack->m_obj
 = v_res_1934_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1935_, lean_object* v_____do__lift_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_1935_, v_____do__lift_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v_____do__lift_1936_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_mkAppB(v___x_1948_, v___y_1949_, v___y_1950_);
return v___x_1951_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1952_, lean_object* v_lhs_1953_, lean_object* v_rhs_1954_, lean_object* v_P_1955_, uint8_t v___x_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
lean_inc_ref(v_lhs_1953_);
lean_inc_ref(v_val_1952_);
v___x_1965_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1952_, v_lhs_1953_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v_fst_1967_; lean_object* v_snd_1968_; lean_object* v___x_1969_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1965_, 1);
v_fst_1967_ = lean_ctor_get(v_a_1966_, 0);
lean_inc(v_fst_1967_);
v_snd_1968_ = lean_ctor_get(v_a_1966_, 1);
lean_inc(v_snd_1968_);
lean_dec(v_a_1966_);
lean_inc_ref(v_rhs_1954_);
lean_inc_ref(v_val_1952_);
v___x_1969_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1952_, v_rhs_1954_, v_snd_1968_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v_fst_1971_; lean_object* v_snd_1972_; lean_object* v___x_1973_; lean_object* v_a_1974_; lean_object* v_fst_1975_; lean_object* v_snd_1976_; lean_object* v_common_1977_; lean_object* v_x_1978_; lean_object* v_y_1979_; lean_object* v___x_1980_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
v_fst_1971_ = lean_ctor_get(v_a_1970_, 0);
lean_inc(v_fst_1971_);
v_snd_1972_ = lean_ctor_get(v_a_1970_, 1);
lean_inc(v_snd_1972_);
lean_dec(v_a_1970_);
v___x_1973_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_1967_, v_fst_1971_, v_snd_1972_);
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1973_);
v_fst_1975_ = lean_ctor_get(v_a_1974_, 0);
lean_inc(v_fst_1975_);
v_snd_1976_ = lean_ctor_get(v_a_1974_, 1);
lean_inc(v_snd_1976_);
lean_dec(v_a_1974_);
v_common_1977_ = lean_ctor_get(v_fst_1975_, 0);
lean_inc_ref(v_common_1977_);
v_x_1978_ = lean_ctor_get(v_fst_1975_, 1);
lean_inc_ref(v_x_1978_);
v_y_1979_ = lean_ctor_get(v_fst_1975_, 2);
lean_inc_ref(v_y_1979_);
lean_dec(v_fst_1975_);
lean_inc_ref(v_val_1952_);
v___x_1980_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_1977_, v_val_1952_, v_snd_1976_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec_ref(v_common_1977_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v_fst_1982_; lean_object* v_snd_1983_; lean_object* v___x_1984_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
v_fst_1982_ = lean_ctor_get(v_a_1981_, 0);
lean_inc(v_fst_1982_);
v_snd_1983_ = lean_ctor_get(v_a_1981_, 1);
lean_inc(v_snd_1983_);
lean_dec(v_a_1981_);
lean_inc_ref(v_val_1952_);
v___x_1984_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_1978_, v_val_1952_, v_snd_1983_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec_ref(v_x_1978_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v_fst_1986_; lean_object* v_snd_1987_; lean_object* v___x_1988_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v_fst_1986_ = lean_ctor_get(v_a_1985_, 0);
lean_inc(v_fst_1986_);
v_snd_1987_ = lean_ctor_get(v_a_1985_, 1);
lean_inc(v_snd_1987_);
lean_dec(v_a_1985_);
lean_inc_ref(v_val_1952_);
v___x_1988_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_1979_, v_val_1952_, v_snd_1987_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec_ref(v_y_1979_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2053_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2053_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2053_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_fst_1993_; lean_object* v_snd_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2052_; 
v_fst_1993_ = lean_ctor_get(v_a_1989_, 0);
v_snd_1994_ = lean_ctor_get(v_a_1989_, 1);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_a_1989_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_1996_ = v_a_1989_;
v_isShared_1997_ = v_isSharedCheck_2052_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_snd_1994_);
lean_inc(v_fst_1993_);
lean_dec(v_a_1989_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2052_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___x_2042_; lean_object* v___f_2043_; lean_object* v___y_2045_; lean_object* v___x_2049_; 
lean_inc_ref(v_val_1952_);
v___x_2042_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_1952_);
v___f_2043_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2043_, 0, v___x_2042_);
lean_inc(v_fst_1982_);
lean_inc_ref(v___f_2043_);
v___x_2049_ = l_Option_merge___redArg(v___f_2043_, v_fst_1982_, v_fst_1986_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v___x_2050_; 
lean_inc_ref(v_val_1952_);
v___x_2050_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1952_);
v___y_2045_ = v___x_2050_;
goto v___jp_2044_;
}
else
{
lean_object* v_val_2051_; 
v_val_2051_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_val_2051_);
lean_dec_ref_known(v___x_2049_, 1);
v___y_2045_ = v_val_2051_;
goto v___jp_2044_;
}
v___jp_1998_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
lean_inc_ref(v_P_1955_);
v___x_2001_ = l_Lean_mkAppB(v_P_1955_, v_lhs_1953_, v_rhs_1954_);
v___x_2002_ = l_Lean_mkAppB(v_P_1955_, v___y_1999_, v___y_2000_);
v___x_2003_ = lean_expr_eqv(v___x_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
lean_del_object(v___x_1991_);
lean_inc_ref(v___x_2002_);
v___x_2004_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_2001_, v___x_2002_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2006_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v___x_2006_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2002_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2018_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2018_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2018_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2011_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2011_, 0, v_a_2007_);
lean_ctor_set(v___x_2011_, 1, v_a_2005_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2, v___x_2003_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*2 + 1, v___x_2003_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2011_);
v___x_2013_ = v___x_1996_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_snd_1994_);
v___x_2013_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2015_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2013_);
v___x_2015_ = v___x_2009_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v_a_2005_);
lean_del_object(v___x_1996_);
lean_dec(v_snd_1994_);
v_a_2019_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2006_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2006_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec_ref(v___x_2002_);
lean_del_object(v___x_1996_);
lean_dec(v_snd_1994_);
v_a_2027_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2004_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2004_);
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
lean_object* v___x_2035_; lean_object* v___x_2037_; 
lean_dec_ref(v___x_2002_);
lean_dec_ref(v___x_2001_);
v___x_2035_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2035_, 0, v___x_1956_);
lean_ctor_set_uint8(v___x_2035_, 1, v___x_1956_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2035_);
v___x_2037_ = v___x_1996_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_snd_1994_);
v___x_2037_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2039_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_2037_);
v___x_2039_ = v___x_1991_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
v___jp_2044_:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Option_merge___redArg(v___f_2043_, v_fst_1982_, v_fst_1993_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1952_);
v___y_1999_ = v___y_2045_;
v___y_2000_ = v___x_2047_;
goto v___jp_1998_;
}
else
{
lean_object* v_val_2048_; 
lean_dec_ref(v_val_1952_);
v_val_2048_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_val_2048_);
lean_dec_ref_known(v___x_2046_, 1);
v___y_1999_ = v___y_2045_;
v___y_2000_ = v_val_2048_;
goto v___jp_1998_;
}
}
}
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v_fst_1986_);
lean_dec(v_fst_1982_);
lean_dec_ref(v_P_1955_);
lean_dec_ref(v_rhs_1954_);
lean_dec_ref(v_lhs_1953_);
lean_dec_ref(v_val_1952_);
v_a_2054_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_1988_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_1988_);
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
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_fst_1982_);
lean_dec_ref(v_y_1979_);
lean_dec_ref(v_P_1955_);
lean_dec_ref(v_rhs_1954_);
lean_dec_ref(v_lhs_1953_);
lean_dec_ref(v_val_1952_);
v_a_2062_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_1984_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_1984_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec_ref(v_y_1979_);
lean_dec_ref(v_x_1978_);
lean_dec_ref(v_P_1955_);
lean_dec_ref(v_rhs_1954_);
lean_dec_ref(v_lhs_1953_);
lean_dec_ref(v_val_1952_);
v_a_2070_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_1980_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_1980_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_fst_1967_);
lean_dec_ref(v_P_1955_);
lean_dec_ref(v_rhs_1954_);
lean_dec_ref(v_lhs_1953_);
lean_dec_ref(v_val_1952_);
v_a_2078_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_1969_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_1969_);
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
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec_ref(v_P_1955_);
lean_dec_ref(v_rhs_1954_);
lean_dec_ref(v_lhs_1953_);
lean_dec_ref(v_val_1952_);
v_a_2086_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_1965_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_1965_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1952_ = stack[0].m_obj;
lean_object* v_lhs_1953_ = stack[1].m_obj;
lean_object* v_rhs_1954_ = stack[2].m_obj;
lean_object* v_P_1955_ = stack[3].m_obj;
uint8_t v___x_1956_ = stack[4].m_num;
lean_object* v___y_1957_ = stack[5].m_obj;
lean_object* v___y_1958_ = stack[6].m_obj;
lean_object* v___y_1959_ = stack[7].m_obj;
lean_object* v___y_1960_ = stack[8].m_obj;
lean_object* v___y_1961_ = stack[9].m_obj;
lean_object* v___y_1962_ = stack[10].m_obj;
lean_object* v___y_1963_ = stack[11].m_obj;
lean_object* v_res_2094_;
v_res_2094_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(v_val_1952_, v_lhs_1953_, v_rhs_1954_, v_P_1955_, v___x_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
stack->m_obj
 = v_res_2094_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_2095_, lean_object* v_lhs_2096_, lean_object* v_rhs_2097_, lean_object* v_P_2098_, lean_object* v___x_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
uint8_t v___x_187721__boxed_2108_; lean_object* v_res_2109_; 
v___x_187721__boxed_2108_ = lean_unbox(v___x_2099_);
v_res_2109_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(v_val_2095_, v_lhs_2096_, v_rhs_2097_, v_P_2098_, v___x_187721__boxed_2108_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
return v_res_2109_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2112_ = l_Lean_stringToMessageData(v___x_2111_);
return v___x_2112_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2113_ = stack[0].m_obj;
lean_object* v___y_2114_ = stack[1].m_obj;
lean_object* v___y_2115_ = stack[2].m_obj;
lean_object* v___y_2116_ = stack[3].m_obj;
lean_object* v___y_2117_ = stack[4].m_obj;
lean_object* v___y_2118_ = stack[5].m_obj;
lean_object* v___y_2119_ = stack[6].m_obj;
lean_object* v___y_2120_ = stack[7].m_obj;
lean_object* v___y_2121_ = stack[8].m_obj;
lean_object* v___y_2122_ = stack[9].m_obj;
lean_object* v_res_2126_;
v_res_2126_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(v_x_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
stack->m_obj
 = v_res_2126_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(v_x_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v_x_2127_);
return v_res_2138_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2139_, lean_object* v_msg_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_ref_2146_; lean_object* v___x_2147_; lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2193_; 
v_ref_2146_ = lean_ctor_get(v___y_2143_, 2);
v___x_2147_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2150_ = v___x_2147_;
v_isShared_2151_ = v_isSharedCheck_2193_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2147_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2193_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v_traceState_2153_; lean_object* v_env_2154_; lean_object* v_nextMacroScope_2155_; lean_object* v_ngen_2156_; lean_object* v_auxDeclNGen_2157_; lean_object* v_cache_2158_; lean_object* v_recordedDeps_2159_; lean_object* v_messages_2160_; lean_object* v_infoState_2161_; lean_object* v_snapshotTasks_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2192_; 
v___x_2152_ = lean_st_ref_take(v___y_2144_);
v_traceState_2153_ = lean_ctor_get(v___x_2152_, 4);
v_env_2154_ = lean_ctor_get(v___x_2152_, 0);
v_nextMacroScope_2155_ = lean_ctor_get(v___x_2152_, 1);
v_ngen_2156_ = lean_ctor_get(v___x_2152_, 2);
v_auxDeclNGen_2157_ = lean_ctor_get(v___x_2152_, 3);
v_cache_2158_ = lean_ctor_get(v___x_2152_, 5);
v_recordedDeps_2159_ = lean_ctor_get(v___x_2152_, 6);
v_messages_2160_ = lean_ctor_get(v___x_2152_, 7);
v_infoState_2161_ = lean_ctor_get(v___x_2152_, 8);
v_snapshotTasks_2162_ = lean_ctor_get(v___x_2152_, 9);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2164_ = v___x_2152_;
v_isShared_2165_ = v_isSharedCheck_2192_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_snapshotTasks_2162_);
lean_inc(v_infoState_2161_);
lean_inc(v_messages_2160_);
lean_inc(v_recordedDeps_2159_);
lean_inc(v_cache_2158_);
lean_inc(v_traceState_2153_);
lean_inc(v_auxDeclNGen_2157_);
lean_inc(v_ngen_2156_);
lean_inc(v_nextMacroScope_2155_);
lean_inc(v_env_2154_);
lean_dec(v___x_2152_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2192_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
uint64_t v_tid_2166_; lean_object* v_traces_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2191_; 
v_tid_2166_ = lean_ctor_get_uint64(v_traceState_2153_, sizeof(void*)*1);
v_traces_2167_ = lean_ctor_get(v_traceState_2153_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_traceState_2153_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2169_ = v_traceState_2153_;
v_isShared_2170_ = v_isSharedCheck_2191_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_traces_2167_);
lean_dec(v_traceState_2153_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2191_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; double v___x_2173_; uint8_t v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2171_ = lean_box(0);
v___x_2172_ = lean_box(0);
v___x_2173_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_2174_ = 0;
v___x_2175_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_2176_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2176_, 0, v_cls_2139_);
lean_ctor_set(v___x_2176_, 1, v___x_2172_);
lean_ctor_set(v___x_2176_, 2, v___x_2175_);
lean_ctor_set_float(v___x_2176_, sizeof(void*)*3, v___x_2173_);
lean_ctor_set_float(v___x_2176_, sizeof(void*)*3 + 8, v___x_2173_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*3 + 16, v___x_2174_);
v___x_2177_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_2178_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2176_);
lean_ctor_set(v___x_2178_, 1, v_a_2148_);
lean_ctor_set(v___x_2178_, 2, v___x_2177_);
lean_inc(v_ref_2146_);
v___x_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2179_, 0, v_ref_2146_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
v___x_2180_ = l_Lean_PersistentArray_push___redArg(v_traces_2167_, v___x_2179_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2180_);
v___x_2182_ = v___x_2169_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2180_);
lean_ctor_set_uint64(v_reuseFailAlloc_2190_, sizeof(void*)*1, v_tid_2166_);
v___x_2182_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2184_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 4, v___x_2182_);
v___x_2184_ = v___x_2164_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_env_2154_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_nextMacroScope_2155_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_ngen_2156_);
lean_ctor_set(v_reuseFailAlloc_2189_, 3, v_auxDeclNGen_2157_);
lean_ctor_set(v_reuseFailAlloc_2189_, 4, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2189_, 5, v_cache_2158_);
lean_ctor_set(v_reuseFailAlloc_2189_, 6, v_recordedDeps_2159_);
lean_ctor_set(v_reuseFailAlloc_2189_, 7, v_messages_2160_);
lean_ctor_set(v_reuseFailAlloc_2189_, 8, v_infoState_2161_);
lean_ctor_set(v_reuseFailAlloc_2189_, 9, v_snapshotTasks_2162_);
v___x_2184_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2185_ = lean_st_ref_put(v___y_2144_, v___x_2184_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2171_);
v___x_2187_ = v___x_2150_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2171_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2139_ = stack[0].m_obj;
lean_object* v_msg_2140_ = stack[1].m_obj;
lean_object* v___y_2141_ = stack[2].m_obj;
lean_object* v___y_2142_ = stack[3].m_obj;
lean_object* v___y_2143_ = stack[4].m_obj;
lean_object* v___y_2144_ = stack[5].m_obj;
lean_object* v_res_2194_;
v_res_2194_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2139_, v_msg_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
stack->m_obj
 = v_res_2194_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2195_, lean_object* v_msg_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2195_, v_msg_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2202_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2205_ = l_Lean_stringToMessageData(v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2));
v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
return v___x_2208_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4));
v___x_2211_ = l_Lean_stringToMessageData(v___x_2210_);
return v___x_2211_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = lean_box(0);
v___x_2213_ = lean_unsigned_to_nat(16u);
v___x_2214_ = lean_mk_array(v___x_2213_, v___x_2212_);
return v___x_2214_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6);
v___x_2216_ = lean_unsigned_to_nat(0u);
v___x_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v___x_2215_);
return v___x_2217_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object* v_lhs_2229_, lean_object* v_rhs_2230_, uint8_t v___x_2231_, lean_object* v___f_2232_, lean_object* v_cls_2233_, lean_object* v_P_2234_, lean_object* v_____r_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2255_; 
lean_inc_ref(v_lhs_2229_);
v___x_2255_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2229_);
if (lean_obj_tag(v___x_2255_) == 1)
{
lean_object* v_val_2256_; lean_object* v___x_2257_; 
v_val_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_val_2256_);
lean_dec_ref_known(v___x_2255_, 1);
lean_inc_ref(v_rhs_2230_);
v___x_2257_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2230_);
if (lean_obj_tag(v___x_2257_) == 1)
{
lean_object* v_val_2258_; uint8_t v___x_2298_; 
v_val_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_val_2258_);
lean_dec_ref_known(v___x_2257_, 1);
v___x_2298_ = lean_expr_eqv(v_val_2256_, v_val_2258_);
if (v___x_2298_ == 0)
{
lean_dec_ref(v_P_2234_);
goto v___jp_2259_;
}
else
{
if (v___x_2231_ == 0)
{
lean_object* v_toCold_2299_; lean_object* v_options_2300_; lean_object* v_inheritedTraceOptions_2301_; uint8_t v_hasTrace_2302_; lean_object* v___x_2303_; lean_object* v___f_2304_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; 
lean_dec(v_val_2258_);
lean_dec_ref(v___f_2232_);
v_toCold_2299_ = lean_ctor_get(v___y_2243_, 0);
v_options_2300_ = lean_ctor_get(v_toCold_2299_, 2);
v_inheritedTraceOptions_2301_ = lean_ctor_get(v_toCold_2299_, 11);
v_hasTrace_2302_ = lean_ctor_get_uint8(v_options_2300_, sizeof(void*)*1);
v___x_2303_ = lean_box(v___x_2231_);
lean_inc(v_val_2256_);
v___f_2304_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_2304_, 0, v_val_2256_);
lean_closure_set(v___f_2304_, 1, v_lhs_2229_);
lean_closure_set(v___f_2304_, 2, v_rhs_2230_);
lean_closure_set(v___f_2304_, 3, v_P_2234_);
lean_closure_set(v___f_2304_, 4, v___x_2303_);
if (v_hasTrace_2302_ == 0)
{
lean_dec(v_cls_2233_);
v___y_2306_ = v___y_2239_;
v___y_2307_ = v___y_2240_;
v___y_2308_ = v___y_2241_;
v___y_2309_ = v___y_2242_;
v___y_2310_ = v___y_2243_;
v___y_2311_ = v___y_2244_;
goto v___jp_2305_;
}
else
{
lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2233_);
v___x_2317_ = l_Lean_Name_append(v___x_2316_, v_cls_2233_);
v___x_2318_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2301_, v_options_2300_, v___x_2317_);
lean_dec(v___x_2317_);
if (v___x_2318_ == 0)
{
lean_dec(v_cls_2233_);
v___y_2306_ = v___y_2239_;
v___y_2307_ = v___y_2240_;
v___y_2308_ = v___y_2241_;
v___y_2309_ = v___y_2242_;
v___y_2310_ = v___y_2243_;
v___y_2311_ = v___y_2244_;
goto v___jp_2305_;
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2319_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_2256_);
v___x_2320_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2256_);
v___x_2321_ = l_Lean_MessageData_ofExpr(v___x_2320_);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2319_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_2324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2233_, v___x_2324_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_dec_ref_known(v___x_2325_, 1);
v___y_2306_ = v___y_2239_;
v___y_2307_ = v___y_2240_;
v___y_2308_ = v___y_2241_;
v___y_2309_ = v___y_2242_;
v___y_2310_ = v___y_2243_;
v___y_2311_ = v___y_2244_;
goto v___jp_2305_;
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v___f_2304_);
lean_dec(v_val_2256_);
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
v___jp_2305_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2312_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2313_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2314_, 0, v_val_2256_);
lean_ctor_set(v___x_2314_, 1, v___x_2312_);
lean_ctor_set(v___x_2314_, 2, v___x_2313_);
v___x_2315_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2304_, v___x_2314_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
return v___x_2315_;
}
}
else
{
lean_dec_ref(v_P_2234_);
goto v___jp_2259_;
}
}
v___jp_2259_:
{
lean_object* v_toCold_2260_; lean_object* v_inheritedTraceOptions_2261_; lean_object* v___x_2262_; 
v_toCold_2260_ = lean_ctor_get(v___y_2243_, 0);
v_inheritedTraceOptions_2261_ = lean_ctor_get(v_toCold_2260_, 11);
lean_inc(v___y_2244_);
lean_inc_ref(v___y_2243_);
lean_inc(v___y_2242_);
lean_inc_ref(v___y_2241_);
lean_inc(v___y_2240_);
lean_inc_ref(v___y_2239_);
lean_inc(v___y_2238_);
lean_inc_ref(v___y_2237_);
lean_inc(v___y_2236_);
lean_inc_ref(v_inheritedTraceOptions_2261_);
v___x_2262_ = lean_apply_11(v___f_2232_, v_inheritedTraceOptions_2261_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, lean_box(0));
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; uint8_t v___x_2264_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = lean_unbox(v_a_2263_);
lean_dec(v_a_2263_);
if (v___x_2264_ == 0)
{
lean_dec(v_val_2258_);
lean_dec(v_val_2256_);
lean_dec(v_cls_2233_);
lean_dec_ref(v_rhs_2230_);
lean_dec_ref(v_lhs_2229_);
goto v___jp_2246_;
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2265_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_2266_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2256_);
v___x_2267_ = l_Lean_MessageData_ofExpr(v___x_2266_);
v___x_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2265_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v___x_2269_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = l_Lean_indentExpr(v_lhs_2229_);
v___x_2272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2258_);
v___x_2276_ = l_Lean_MessageData_ofExpr(v___x_2275_);
v___x_2277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2274_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v___x_2269_);
v___x_2279_ = l_Lean_indentExpr(v_rhs_2230_);
v___x_2280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2233_, v___x_2280_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_dec_ref_known(v___x_2281_, 1);
goto v___jp_2246_;
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2281_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2281_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_val_2258_);
lean_dec(v_val_2256_);
lean_dec(v_cls_2233_);
lean_dec_ref(v_rhs_2230_);
lean_dec_ref(v_lhs_2229_);
v_a_2290_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2262_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2262_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
else
{
lean_object* v_toCold_2334_; lean_object* v_inheritedTraceOptions_2335_; lean_object* v___x_2336_; 
lean_dec(v___x_2257_);
lean_dec(v_val_2256_);
lean_dec_ref(v_P_2234_);
lean_dec_ref(v_lhs_2229_);
v_toCold_2334_ = lean_ctor_get(v___y_2243_, 0);
v_inheritedTraceOptions_2335_ = lean_ctor_get(v_toCold_2334_, 11);
lean_inc(v___y_2244_);
lean_inc_ref(v___y_2243_);
lean_inc(v___y_2242_);
lean_inc_ref(v___y_2241_);
lean_inc(v___y_2240_);
lean_inc_ref(v___y_2239_);
lean_inc(v___y_2238_);
lean_inc_ref(v___y_2237_);
lean_inc(v___y_2236_);
lean_inc_ref(v_inheritedTraceOptions_2335_);
v___x_2336_ = lean_apply_11(v___f_2232_, v_inheritedTraceOptions_2335_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, lean_box(0));
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; uint8_t v___x_2338_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = lean_unbox(v_a_2337_);
lean_dec(v_a_2337_);
if (v___x_2338_ == 0)
{
lean_dec(v_cls_2233_);
lean_dec_ref(v_rhs_2230_);
goto v___jp_2249_;
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2339_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2340_ = l_Lean_indentExpr(v_rhs_2230_);
v___x_2341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
v___x_2342_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2233_, v___x_2341_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_dec_ref_known(v___x_2342_, 1);
goto v___jp_2249_;
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec(v_cls_2233_);
lean_dec_ref(v_rhs_2230_);
v_a_2351_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2336_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2336_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
else
{
lean_object* v_toCold_2359_; lean_object* v_inheritedTraceOptions_2360_; lean_object* v___x_2361_; 
lean_dec(v___x_2255_);
lean_dec_ref(v_P_2234_);
lean_dec_ref(v_rhs_2230_);
v_toCold_2359_ = lean_ctor_get(v___y_2243_, 0);
v_inheritedTraceOptions_2360_ = lean_ctor_get(v_toCold_2359_, 11);
lean_inc(v___y_2244_);
lean_inc_ref(v___y_2243_);
lean_inc(v___y_2242_);
lean_inc_ref(v___y_2241_);
lean_inc(v___y_2240_);
lean_inc_ref(v___y_2239_);
lean_inc(v___y_2238_);
lean_inc_ref(v___y_2237_);
lean_inc(v___y_2236_);
lean_inc_ref(v_inheritedTraceOptions_2360_);
v___x_2361_ = lean_apply_11(v___f_2232_, v_inheritedTraceOptions_2360_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, lean_box(0));
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; uint8_t v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = lean_unbox(v_a_2362_);
lean_dec(v_a_2362_);
if (v___x_2363_ == 0)
{
lean_dec(v_cls_2233_);
lean_dec_ref(v_lhs_2229_);
goto v___jp_2252_;
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2364_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2365_ = l_Lean_indentExpr(v_lhs_2229_);
v___x_2366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2233_, v___x_2366_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_dec_ref_known(v___x_2367_, 1);
goto v___jp_2252_;
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec(v_cls_2233_);
lean_dec_ref(v_lhs_2229_);
v_a_2376_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2361_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2361_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
v___jp_2246_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2247_, 0, v___x_2231_);
lean_ctor_set_uint8(v___x_2247_, 1, v___x_2231_);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
return v___x_2248_;
}
v___jp_2249_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2250_, 0, v___x_2231_);
lean_ctor_set_uint8(v___x_2250_, 1, v___x_2231_);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
return v___x_2251_;
}
v___jp_2252_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2253_, 0, v___x_2231_);
lean_ctor_set_uint8(v___x_2253_, 1, v___x_2231_);
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
return v___x_2254_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_2229_ = stack[0].m_obj;
lean_object* v_rhs_2230_ = stack[1].m_obj;
uint8_t v___x_2231_ = stack[2].m_num;
lean_object* v___f_2232_ = stack[3].m_obj;
lean_object* v_cls_2233_ = stack[4].m_obj;
lean_object* v_P_2234_ = stack[5].m_obj;
lean_object* v_____r_2235_ = stack[6].m_obj;
lean_object* v___y_2236_ = stack[7].m_obj;
lean_object* v___y_2237_ = stack[8].m_obj;
lean_object* v___y_2238_ = stack[9].m_obj;
lean_object* v___y_2239_ = stack[10].m_obj;
lean_object* v___y_2240_ = stack[11].m_obj;
lean_object* v___y_2241_ = stack[12].m_obj;
lean_object* v___y_2242_ = stack[13].m_obj;
lean_object* v___y_2243_ = stack[14].m_obj;
lean_object* v___y_2244_ = stack[15].m_obj;
lean_object* v_res_2384_;
v_res_2384_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2229_, v_rhs_2230_, v___x_2231_, v___f_2232_, v_cls_2233_, v_P_2234_, v_____r_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
stack->m_obj
 = v_res_2384_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object** _args){
lean_object* v_lhs_2385_ = _args[0];
lean_object* v_rhs_2386_ = _args[1];
lean_object* v___x_2387_ = _args[2];
lean_object* v___f_2388_ = _args[3];
lean_object* v_cls_2389_ = _args[4];
lean_object* v_P_2390_ = _args[5];
lean_object* v_____r_2391_ = _args[6];
lean_object* v___y_2392_ = _args[7];
lean_object* v___y_2393_ = _args[8];
lean_object* v___y_2394_ = _args[9];
lean_object* v___y_2395_ = _args[10];
lean_object* v___y_2396_ = _args[11];
lean_object* v___y_2397_ = _args[12];
lean_object* v___y_2398_ = _args[13];
lean_object* v___y_2399_ = _args[14];
lean_object* v___y_2400_ = _args[15];
lean_object* v___y_2401_ = _args[16];
_start:
{
uint8_t v___x_188426__boxed_2402_; lean_object* v_res_2403_; 
v___x_188426__boxed_2402_ = lean_unbox(v___x_2387_);
v_res_2403_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2385_, v_rhs_2386_, v___x_188426__boxed_2402_, v___f_2388_, v_cls_2389_, v_P_2390_, v_____r_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
return v_res_2403_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(lean_object* v_val_2404_, lean_object* v_lhs_2405_, lean_object* v_rhs_2406_, lean_object* v_P_2407_, uint8_t v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; 
lean_inc_ref(v_lhs_2405_);
lean_inc_ref(v_val_2404_);
v___x_2417_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2404_, v_lhs_2405_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v_fst_2419_; lean_object* v_snd_2420_; lean_object* v___x_2421_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v_fst_2419_ = lean_ctor_get(v_a_2418_, 0);
lean_inc(v_fst_2419_);
v_snd_2420_ = lean_ctor_get(v_a_2418_, 1);
lean_inc(v_snd_2420_);
lean_dec(v_a_2418_);
lean_inc_ref(v_rhs_2406_);
lean_inc_ref(v_val_2404_);
v___x_2421_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_2404_, v_rhs_2406_, v_snd_2420_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v_fst_2423_; lean_object* v_snd_2424_; lean_object* v___x_2425_; lean_object* v_a_2426_; lean_object* v_fst_2427_; lean_object* v_snd_2428_; lean_object* v_common_2429_; lean_object* v_x_2430_; lean_object* v_y_2431_; lean_object* v___x_2432_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2421_, 1);
v_fst_2423_ = lean_ctor_get(v_a_2422_, 0);
lean_inc(v_fst_2423_);
v_snd_2424_ = lean_ctor_get(v_a_2422_, 1);
lean_inc(v_snd_2424_);
lean_dec(v_a_2422_);
v___x_2425_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_2419_, v_fst_2423_, v_snd_2424_);
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref(v___x_2425_);
v_fst_2427_ = lean_ctor_get(v_a_2426_, 0);
lean_inc(v_fst_2427_);
v_snd_2428_ = lean_ctor_get(v_a_2426_, 1);
lean_inc(v_snd_2428_);
lean_dec(v_a_2426_);
v_common_2429_ = lean_ctor_get(v_fst_2427_, 0);
lean_inc_ref(v_common_2429_);
v_x_2430_ = lean_ctor_get(v_fst_2427_, 1);
lean_inc_ref(v_x_2430_);
v_y_2431_ = lean_ctor_get(v_fst_2427_, 2);
lean_inc_ref(v_y_2431_);
lean_dec(v_fst_2427_);
lean_inc_ref(v_val_2404_);
v___x_2432_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_2429_, v_val_2404_, v_snd_2428_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec_ref(v_common_2429_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v_fst_2434_; lean_object* v_snd_2435_; lean_object* v___x_2436_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
v_fst_2434_ = lean_ctor_get(v_a_2433_, 0);
lean_inc(v_fst_2434_);
v_snd_2435_ = lean_ctor_get(v_a_2433_, 1);
lean_inc(v_snd_2435_);
lean_dec(v_a_2433_);
lean_inc_ref(v_val_2404_);
v___x_2436_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_2430_, v_val_2404_, v_snd_2435_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec_ref(v_x_2430_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v_fst_2438_; lean_object* v_snd_2439_; lean_object* v___x_2440_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2436_, 1);
v_fst_2438_ = lean_ctor_get(v_a_2437_, 0);
lean_inc(v_fst_2438_);
v_snd_2439_ = lean_ctor_get(v_a_2437_, 1);
lean_inc(v_snd_2439_);
lean_dec(v_a_2437_);
lean_inc_ref(v_val_2404_);
v___x_2440_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_2431_, v_val_2404_, v_snd_2439_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec_ref(v_y_2431_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2505_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2505_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2505_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v_fst_2445_; lean_object* v_snd_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2504_; 
v_fst_2445_ = lean_ctor_get(v_a_2441_, 0);
v_snd_2446_ = lean_ctor_get(v_a_2441_, 1);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_a_2441_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2448_ = v_a_2441_;
v_isShared_2449_ = v_isSharedCheck_2504_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_snd_2446_);
lean_inc(v_fst_2445_);
lean_dec(v_a_2441_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2504_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___x_2494_; lean_object* v___f_2495_; lean_object* v___y_2497_; lean_object* v___x_2501_; 
lean_inc_ref(v_val_2404_);
v___x_2494_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2404_);
v___f_2495_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2495_, 0, v___x_2494_);
lean_inc(v_fst_2434_);
lean_inc_ref(v___f_2495_);
v___x_2501_ = l_Option_merge___redArg(v___f_2495_, v_fst_2434_, v_fst_2438_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v___x_2502_; 
lean_inc_ref(v_val_2404_);
v___x_2502_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2404_);
v___y_2497_ = v___x_2502_;
goto v___jp_2496_;
}
else
{
lean_object* v_val_2503_; 
v_val_2503_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_val_2503_);
lean_dec_ref_known(v___x_2501_, 1);
v___y_2497_ = v_val_2503_;
goto v___jp_2496_;
}
v___jp_2450_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
lean_inc_ref(v_P_2407_);
v___x_2453_ = l_Lean_mkAppB(v_P_2407_, v_lhs_2405_, v_rhs_2406_);
v___x_2454_ = l_Lean_mkAppB(v_P_2407_, v___y_2451_, v___y_2452_);
v___x_2455_ = lean_expr_eqv(v___x_2453_, v___x_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
lean_del_object(v___x_2443_);
lean_inc_ref(v___x_2454_);
v___x_2456_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_2453_, v___x_2454_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2458_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v___x_2458_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2454_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2470_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2470_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2470_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2463_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2463_, 0, v_a_2459_);
lean_ctor_set(v___x_2463_, 1, v_a_2457_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*2, v___x_2455_);
lean_ctor_set_uint8(v___x_2463_, sizeof(void*)*2 + 1, v___x_2455_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2463_);
v___x_2465_ = v___x_2448_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_snd_2446_);
v___x_2465_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2467_; 
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2465_);
v___x_2467_ = v___x_2461_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
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
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec(v_a_2457_);
lean_del_object(v___x_2448_);
lean_dec(v_snd_2446_);
v_a_2471_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2458_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2458_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v___x_2454_);
lean_del_object(v___x_2448_);
lean_dec(v_snd_2446_);
v_a_2479_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2456_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2456_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
lean_object* v___x_2487_; lean_object* v___x_2489_; 
lean_dec_ref(v___x_2454_);
lean_dec_ref(v___x_2453_);
v___x_2487_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2487_, 0, v___y_2408_);
lean_ctor_set_uint8(v___x_2487_, 1, v___y_2408_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2487_);
v___x_2489_ = v___x_2448_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_snd_2446_);
v___x_2489_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2491_; 
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2489_);
v___x_2491_ = v___x_2443_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
v___jp_2496_:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Option_merge___redArg(v___f_2495_, v_fst_2434_, v_fst_2445_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_2404_);
v___y_2451_ = v___y_2497_;
v___y_2452_ = v___x_2499_;
goto v___jp_2450_;
}
else
{
lean_object* v_val_2500_; 
lean_dec_ref(v_val_2404_);
v_val_2500_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_val_2500_);
lean_dec_ref_known(v___x_2498_, 1);
v___y_2451_ = v___y_2497_;
v___y_2452_ = v_val_2500_;
goto v___jp_2450_;
}
}
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_fst_2438_);
lean_dec(v_fst_2434_);
lean_dec_ref(v_P_2407_);
lean_dec_ref(v_rhs_2406_);
lean_dec_ref(v_lhs_2405_);
lean_dec_ref(v_val_2404_);
v_a_2506_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2440_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2440_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v_fst_2434_);
lean_dec_ref(v_y_2431_);
lean_dec_ref(v_P_2407_);
lean_dec_ref(v_rhs_2406_);
lean_dec_ref(v_lhs_2405_);
lean_dec_ref(v_val_2404_);
v_a_2514_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2436_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2436_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec_ref(v_y_2431_);
lean_dec_ref(v_x_2430_);
lean_dec_ref(v_P_2407_);
lean_dec_ref(v_rhs_2406_);
lean_dec_ref(v_lhs_2405_);
lean_dec_ref(v_val_2404_);
v_a_2522_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2432_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2432_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec(v_fst_2419_);
lean_dec_ref(v_P_2407_);
lean_dec_ref(v_rhs_2406_);
lean_dec_ref(v_lhs_2405_);
lean_dec_ref(v_val_2404_);
v_a_2530_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2421_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2421_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
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
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec_ref(v_P_2407_);
lean_dec_ref(v_rhs_2406_);
lean_dec_ref(v_lhs_2405_);
lean_dec_ref(v_val_2404_);
v_a_2538_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2417_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2417_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2404_ = stack[0].m_obj;
lean_object* v_lhs_2405_ = stack[1].m_obj;
lean_object* v_rhs_2406_ = stack[2].m_obj;
lean_object* v_P_2407_ = stack[3].m_obj;
uint8_t v___y_2408_ = stack[4].m_num;
lean_object* v___y_2409_ = stack[5].m_obj;
lean_object* v___y_2410_ = stack[6].m_obj;
lean_object* v___y_2411_ = stack[7].m_obj;
lean_object* v___y_2412_ = stack[8].m_obj;
lean_object* v___y_2413_ = stack[9].m_obj;
lean_object* v___y_2414_ = stack[10].m_obj;
lean_object* v___y_2415_ = stack[11].m_obj;
lean_object* v_res_2546_;
v_res_2546_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(v_val_2404_, v_lhs_2405_, v_rhs_2406_, v_P_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
stack->m_obj
 = v_res_2546_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed(lean_object* v_val_2547_, lean_object* v_lhs_2548_, lean_object* v_rhs_2549_, lean_object* v_P_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
uint8_t v___y_188937__boxed_2560_; lean_object* v_res_2561_; 
v___y_188937__boxed_2560_ = lean_unbox(v___y_2551_);
v_res_2561_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5(v_val_2547_, v_lhs_2548_, v_rhs_2549_, v_P_2550_, v___y_188937__boxed_2560_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
return v_res_2561_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(lean_object* v_lhs_2562_, lean_object* v_rhs_2563_, lean_object* v_P_2564_, lean_object* v_cls_2565_, uint8_t v___x_2566_, lean_object* v___f_2567_, uint8_t v___x_2568_, lean_object* v_____r_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2586_; 
lean_inc_ref(v_lhs_2562_);
v___x_2586_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2562_);
if (lean_obj_tag(v___x_2586_) == 1)
{
lean_object* v_val_2587_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; uint8_t v___y_2601_; lean_object* v___x_2626_; 
v_val_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_val_2587_);
lean_dec_ref_known(v___x_2586_, 1);
lean_inc_ref(v_rhs_2563_);
v___x_2626_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2563_);
if (lean_obj_tag(v___x_2626_) == 1)
{
lean_object* v_val_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2675_; 
v_val_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2675_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_val_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2675_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
uint8_t v___x_2631_; 
v___x_2631_ = lean_expr_eqv(v_val_2587_, v_val_2627_);
if (v___x_2631_ == 0)
{
if (v___x_2566_ == 0)
{
lean_del_object(v___x_2629_);
lean_dec(v_val_2627_);
lean_dec_ref(v___f_2567_);
v___y_2601_ = v___x_2566_;
goto v___jp_2600_;
}
else
{
lean_object* v_toCold_2637_; lean_object* v_inheritedTraceOptions_2638_; lean_object* v___x_2639_; 
lean_dec_ref(v_P_2564_);
v_toCold_2637_ = lean_ctor_get(v___y_2577_, 0);
v_inheritedTraceOptions_2638_ = lean_ctor_get(v_toCold_2637_, 11);
lean_inc(v___y_2578_);
lean_inc_ref(v___y_2577_);
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
lean_inc(v___y_2574_);
lean_inc_ref(v___y_2573_);
lean_inc(v___y_2572_);
lean_inc_ref(v___y_2571_);
lean_inc(v___y_2570_);
lean_inc_ref(v_inheritedTraceOptions_2638_);
v___x_2639_ = lean_apply_11(v___f_2567_, v_inheritedTraceOptions_2638_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, lean_box(0));
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; uint8_t v___x_2641_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2639_, 1);
v___x_2641_ = lean_unbox(v_a_2640_);
lean_dec(v_a_2640_);
if (v___x_2641_ == 0)
{
lean_dec(v_val_2627_);
lean_dec(v_val_2587_);
lean_dec(v_cls_2565_);
lean_dec_ref(v_rhs_2563_);
lean_dec_ref(v_lhs_2562_);
goto v___jp_2632_;
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2642_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_2643_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2587_);
v___x_2644_ = l_Lean_MessageData_ofExpr(v___x_2643_);
v___x_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2642_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_2647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2645_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
v___x_2648_ = l_Lean_indentExpr(v_lhs_2562_);
v___x_2649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2647_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
v___x_2650_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_2651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2649_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2627_);
v___x_2653_ = l_Lean_MessageData_ofExpr(v___x_2652_);
v___x_2654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2651_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
lean_ctor_set(v___x_2655_, 1, v___x_2646_);
v___x_2656_ = l_Lean_indentExpr(v_rhs_2563_);
v___x_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2655_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2565_, v___x_2657_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_dec_ref_known(v___x_2658_, 1);
goto v___jp_2632_;
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_del_object(v___x_2629_);
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
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
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_del_object(v___x_2629_);
lean_dec(v_val_2627_);
lean_dec(v_val_2587_);
lean_dec(v_cls_2565_);
lean_dec_ref(v_rhs_2563_);
lean_dec_ref(v_lhs_2562_);
v_a_2667_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2639_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2639_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
else
{
lean_del_object(v___x_2629_);
lean_dec(v_val_2627_);
lean_dec_ref(v___f_2567_);
v___y_2601_ = v___x_2568_;
goto v___jp_2600_;
}
v___jp_2632_:
{
lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2633_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2633_, 0, v___x_2631_);
lean_ctor_set_uint8(v___x_2633_, 1, v___x_2631_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set_tag(v___x_2629_, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2633_);
v___x_2635_ = v___x_2629_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
else
{
lean_object* v_toCold_2676_; lean_object* v_inheritedTraceOptions_2677_; lean_object* v___x_2678_; 
lean_dec(v___x_2626_);
lean_dec(v_val_2587_);
lean_dec_ref(v_P_2564_);
lean_dec_ref(v_lhs_2562_);
v_toCold_2676_ = lean_ctor_get(v___y_2577_, 0);
v_inheritedTraceOptions_2677_ = lean_ctor_get(v_toCold_2676_, 11);
lean_inc(v___y_2578_);
lean_inc_ref(v___y_2577_);
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
lean_inc(v___y_2574_);
lean_inc_ref(v___y_2573_);
lean_inc(v___y_2572_);
lean_inc_ref(v___y_2571_);
lean_inc(v___y_2570_);
lean_inc_ref(v_inheritedTraceOptions_2677_);
v___x_2678_ = lean_apply_11(v___f_2567_, v_inheritedTraceOptions_2677_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, lean_box(0));
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; uint8_t v___x_2680_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2680_ = lean_unbox(v_a_2679_);
lean_dec(v_a_2679_);
if (v___x_2680_ == 0)
{
lean_dec(v_cls_2565_);
lean_dec_ref(v_rhs_2563_);
goto v___jp_2580_;
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2681_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2682_ = l_Lean_indentExpr(v_rhs_2563_);
v___x_2683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2681_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2565_, v___x_2683_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_dec_ref_known(v___x_2684_, 1);
goto v___jp_2580_;
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec(v_cls_2565_);
lean_dec_ref(v_rhs_2563_);
v_a_2693_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2678_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2678_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
v___jp_2588_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2596_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2597_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_2598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2598_, 0, v_val_2587_);
lean_ctor_set(v___x_2598_, 1, v___x_2596_);
lean_ctor_set(v___x_2598_, 2, v___x_2597_);
v___x_2599_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2589_, v___x_2598_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
return v___x_2599_;
}
v___jp_2600_:
{
lean_object* v_toCold_2602_; lean_object* v_options_2603_; lean_object* v_inheritedTraceOptions_2604_; uint8_t v_hasTrace_2605_; lean_object* v___x_2606_; lean_object* v___f_2607_; 
v_toCold_2602_ = lean_ctor_get(v___y_2577_, 0);
v_options_2603_ = lean_ctor_get(v_toCold_2602_, 2);
v_inheritedTraceOptions_2604_ = lean_ctor_get(v_toCold_2602_, 11);
v_hasTrace_2605_ = lean_ctor_get_uint8(v_options_2603_, sizeof(void*)*1);
v___x_2606_ = lean_box(v___y_2601_);
lean_inc(v_val_2587_);
v___f_2607_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__5___boxed), 13, 5);
lean_closure_set(v___f_2607_, 0, v_val_2587_);
lean_closure_set(v___f_2607_, 1, v_lhs_2562_);
lean_closure_set(v___f_2607_, 2, v_rhs_2563_);
lean_closure_set(v___f_2607_, 3, v_P_2564_);
lean_closure_set(v___f_2607_, 4, v___x_2606_);
if (v_hasTrace_2605_ == 0)
{
lean_dec(v_cls_2565_);
v___y_2589_ = v___f_2607_;
v___y_2590_ = v___y_2573_;
v___y_2591_ = v___y_2574_;
v___y_2592_ = v___y_2575_;
v___y_2593_ = v___y_2576_;
v___y_2594_ = v___y_2577_;
v___y_2595_ = v___y_2578_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2565_);
v___x_2609_ = l_Lean_Name_append(v___x_2608_, v_cls_2565_);
v___x_2610_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2604_, v_options_2603_, v___x_2609_);
lean_dec(v___x_2609_);
if (v___x_2610_ == 0)
{
lean_dec(v_cls_2565_);
v___y_2589_ = v___f_2607_;
v___y_2590_ = v___y_2573_;
v___y_2591_ = v___y_2574_;
v___y_2592_ = v___y_2575_;
v___y_2593_ = v___y_2576_;
v___y_2594_ = v___y_2577_;
v___y_2595_ = v___y_2578_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2611_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_2587_);
v___x_2612_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2587_);
v___x_2613_ = l_Lean_MessageData_ofExpr(v___x_2612_);
v___x_2614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2611_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_2616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2614_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2565_, v___x_2616_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_dec_ref_known(v___x_2617_, 1);
v___y_2589_ = v___f_2607_;
v___y_2590_ = v___y_2573_;
v___y_2591_ = v___y_2574_;
v___y_2592_ = v___y_2575_;
v___y_2593_ = v___y_2576_;
v___y_2594_ = v___y_2577_;
v___y_2595_ = v___y_2578_;
goto v___jp_2588_;
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref(v___f_2607_);
lean_dec(v_val_2587_);
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_2701_; lean_object* v_inheritedTraceOptions_2702_; lean_object* v___x_2703_; 
lean_dec(v___x_2586_);
lean_dec_ref(v_P_2564_);
lean_dec_ref(v_rhs_2563_);
v_toCold_2701_ = lean_ctor_get(v___y_2577_, 0);
v_inheritedTraceOptions_2702_ = lean_ctor_get(v_toCold_2701_, 11);
lean_inc(v___y_2578_);
lean_inc_ref(v___y_2577_);
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
lean_inc(v___y_2574_);
lean_inc_ref(v___y_2573_);
lean_inc(v___y_2572_);
lean_inc_ref(v___y_2571_);
lean_inc(v___y_2570_);
lean_inc_ref(v_inheritedTraceOptions_2702_);
v___x_2703_ = lean_apply_11(v___f_2567_, v_inheritedTraceOptions_2702_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, lean_box(0));
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; uint8_t v___x_2705_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
v___x_2705_ = lean_unbox(v_a_2704_);
lean_dec(v_a_2704_);
if (v___x_2705_ == 0)
{
lean_dec(v_cls_2565_);
lean_dec_ref(v_lhs_2562_);
goto v___jp_2583_;
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2706_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_2707_ = l_Lean_indentExpr(v_lhs_2562_);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2565_, v___x_2708_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_dec_ref_known(v___x_2709_, 1);
goto v___jp_2583_;
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_cls_2565_);
lean_dec_ref(v_lhs_2562_);
v_a_2718_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2703_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2703_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
v___jp_2580_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2581_, 0, v___x_2568_);
lean_ctor_set_uint8(v___x_2581_, 1, v___x_2568_);
v___x_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
return v___x_2582_;
}
v___jp_2583_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2584_, 0, v___x_2568_);
lean_ctor_set_uint8(v___x_2584_, 1, v___x_2568_);
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
return v___x_2585_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_2562_ = stack[0].m_obj;
lean_object* v_rhs_2563_ = stack[1].m_obj;
lean_object* v_P_2564_ = stack[2].m_obj;
lean_object* v_cls_2565_ = stack[3].m_obj;
uint8_t v___x_2566_ = stack[4].m_num;
lean_object* v___f_2567_ = stack[5].m_obj;
uint8_t v___x_2568_ = stack[6].m_num;
lean_object* v_____r_2569_ = stack[7].m_obj;
lean_object* v___y_2570_ = stack[8].m_obj;
lean_object* v___y_2571_ = stack[9].m_obj;
lean_object* v___y_2572_ = stack[10].m_obj;
lean_object* v___y_2573_ = stack[11].m_obj;
lean_object* v___y_2574_ = stack[12].m_obj;
lean_object* v___y_2575_ = stack[13].m_obj;
lean_object* v___y_2576_ = stack[14].m_obj;
lean_object* v___y_2577_ = stack[15].m_obj;
lean_object* v___y_2578_ = stack[16].m_obj;
lean_object* v_res_2726_;
v_res_2726_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2562_, v_rhs_2563_, v_P_2564_, v_cls_2565_, v___x_2566_, v___f_2567_, v___x_2568_, v_____r_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
stack->m_obj
 = v_res_2726_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4___boxed(lean_object** _args){
lean_object* v_lhs_2727_ = _args[0];
lean_object* v_rhs_2728_ = _args[1];
lean_object* v_P_2729_ = _args[2];
lean_object* v_cls_2730_ = _args[3];
lean_object* v___x_2731_ = _args[4];
lean_object* v___f_2732_ = _args[5];
lean_object* v___x_2733_ = _args[6];
lean_object* v_____r_2734_ = _args[7];
lean_object* v___y_2735_ = _args[8];
lean_object* v___y_2736_ = _args[9];
lean_object* v___y_2737_ = _args[10];
lean_object* v___y_2738_ = _args[11];
lean_object* v___y_2739_ = _args[12];
lean_object* v___y_2740_ = _args[13];
lean_object* v___y_2741_ = _args[14];
lean_object* v___y_2742_ = _args[15];
lean_object* v___y_2743_ = _args[16];
lean_object* v___y_2744_ = _args[17];
_start:
{
uint8_t v___x_189408__boxed_2745_; uint8_t v___x_189410__boxed_2746_; lean_object* v_res_2747_; 
v___x_189408__boxed_2745_ = lean_unbox(v___x_2731_);
v___x_189410__boxed_2746_ = lean_unbox(v___x_2733_);
v_res_2747_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_2727_, v_rhs_2728_, v_P_2729_, v_cls_2730_, v___x_189408__boxed_2745_, v___f_2732_, v___x_189410__boxed_2746_, v_____r_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
return v_res_2747_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_e_2748_){
_start:
{
if (lean_obj_tag(v_e_2748_) == 0)
{
uint8_t v___x_2749_; 
v___x_2749_ = 2;
return v___x_2749_;
}
else
{
uint8_t v___x_2750_; 
v___x_2750_ = 0;
return v___x_2750_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2748_ = stack[0].m_obj;
uint8_t v_res_2751_;
v_res_2751_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_e_2748_);
stack->m_num = v_res_2751_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_e_2752_){
_start:
{
uint8_t v_res_2753_; lean_object* v_r_2754_; 
v_res_2753_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_e_2752_);
lean_dec_ref(v_e_2752_);
v_r_2754_ = lean_box(v_res_2753_);
return v_r_2754_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_x_2755_){
_start:
{
if (lean_obj_tag(v_x_2755_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
v_a_2757_ = lean_ctor_get(v_x_2755_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_x_2755_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v_x_2755_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v_x_2755_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set_tag(v___x_2759_, 1);
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
v_a_2765_ = lean_ctor_get(v_x_2755_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_x_2755_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v_x_2755_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v_x_2755_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set_tag(v___x_2767_, 0);
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2755_ = stack[0].m_obj;
lean_object* v_res_2773_;
v_res_2773_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_2755_);
stack->m_obj
 = v_res_2773_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_x_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_2774_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2777_, lean_object* v_opt_2778_){
_start:
{
lean_object* v_name_2779_; lean_object* v_defValue_2780_; lean_object* v_map_2781_; lean_object* v___x_2782_; 
v_name_2779_ = lean_ctor_get(v_opt_2778_, 0);
v_defValue_2780_ = lean_ctor_get(v_opt_2778_, 1);
v_map_2781_ = lean_ctor_get(v_opts_2777_, 0);
v___x_2782_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2781_, v_name_2779_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_inc(v_defValue_2780_);
return v_defValue_2780_;
}
else
{
lean_object* v_val_2783_; 
v_val_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_val_2783_);
lean_dec_ref_known(v___x_2782_, 1);
if (lean_obj_tag(v_val_2783_) == 3)
{
lean_object* v_v_2784_; 
v_v_2784_ = lean_ctor_get(v_val_2783_, 0);
lean_inc(v_v_2784_);
lean_dec_ref_known(v_val_2783_, 1);
return v_v_2784_;
}
else
{
lean_dec(v_val_2783_);
lean_inc(v_defValue_2780_);
return v_defValue_2780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2785_, lean_object* v_opt_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2785_, v_opt_2786_);
lean_dec_ref(v_opt_2786_);
lean_dec_ref(v_opts_2785_);
return v_res_2787_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t v_sz_2788_, size_t v_i_2789_, lean_object* v_bs_2790_){
_start:
{
uint8_t v___x_2791_; 
v___x_2791_ = lean_usize_dec_lt(v_i_2789_, v_sz_2788_);
if (v___x_2791_ == 0)
{
return v_bs_2790_;
}
else
{
lean_object* v_v_2792_; lean_object* v_msg_2793_; lean_object* v___x_2794_; lean_object* v_bs_x27_2795_; size_t v___x_2796_; size_t v___x_2797_; lean_object* v___x_2798_; 
v_v_2792_ = lean_array_uget_borrowed(v_bs_2790_, v_i_2789_);
v_msg_2793_ = lean_ctor_get(v_v_2792_, 1);
lean_inc_ref(v_msg_2793_);
v___x_2794_ = lean_unsigned_to_nat(0u);
v_bs_x27_2795_ = lean_array_uset(v_bs_2790_, v_i_2789_, v___x_2794_);
v___x_2796_ = ((size_t)1ULL);
v___x_2797_ = lean_usize_add(v_i_2789_, v___x_2796_);
v___x_2798_ = lean_array_uset(v_bs_x27_2795_, v_i_2789_, v_msg_2793_);
v_i_2789_ = v___x_2797_;
v_bs_2790_ = v___x_2798_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2788_ = stack[0].m_num;
size_t v_i_2789_ = stack[1].m_num;
lean_object* v_bs_2790_ = stack[2].m_obj;
lean_object* v_res_2800_;
v_res_2800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_2788_, v_i_2789_, v_bs_2790_);
stack->m_obj
 = v_res_2800_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2801_, lean_object* v_i_2802_, lean_object* v_bs_2803_){
_start:
{
size_t v_sz_boxed_2804_; size_t v_i_boxed_2805_; lean_object* v_res_2806_; 
v_sz_boxed_2804_ = lean_unbox_usize(v_sz_2801_);
lean_dec(v_sz_2801_);
v_i_boxed_2805_ = lean_unbox_usize(v_i_2802_);
lean_dec(v_i_2802_);
v_res_2806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_boxed_2804_, v_i_boxed_2805_, v_bs_2803_);
return v_res_2806_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object* v_oldTraces_2807_, lean_object* v_data_2808_, lean_object* v_ref_2809_, lean_object* v_msg_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_toCold_2816_; lean_object* v_currRecDepth_2817_; lean_object* v_ref_2818_; uint16_t v_optionFlags_2819_; uint8_t v_suppressElabErrors_2820_; uint8_t v_isRecordingDeps_2821_; lean_object* v_ref_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v_traceState_2825_; lean_object* v_traces_2826_; lean_object* v___x_2827_; size_t v_sz_2828_; size_t v___x_2829_; lean_object* v___x_2830_; lean_object* v_msg_2831_; lean_object* v___x_2832_; lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2871_; 
v_toCold_2816_ = lean_ctor_get(v___y_2813_, 0);
v_currRecDepth_2817_ = lean_ctor_get(v___y_2813_, 1);
v_ref_2818_ = lean_ctor_get(v___y_2813_, 2);
v_optionFlags_2819_ = lean_ctor_get_uint16(v___y_2813_, sizeof(void*)*3);
v_suppressElabErrors_2820_ = lean_ctor_get_uint8(v___y_2813_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2821_ = lean_ctor_get_uint8(v___y_2813_, sizeof(void*)*3 + 3);
v_ref_2822_ = l_Lean_replaceRef(v_ref_2809_, v_ref_2818_);
lean_inc(v_currRecDepth_2817_);
lean_inc_ref(v_toCold_2816_);
v___x_2823_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2823_, 0, v_toCold_2816_);
lean_ctor_set(v___x_2823_, 1, v_currRecDepth_2817_);
lean_ctor_set(v___x_2823_, 2, v_ref_2822_);
lean_ctor_set_uint16(v___x_2823_, sizeof(void*)*3, v_optionFlags_2819_);
lean_ctor_set_uint8(v___x_2823_, sizeof(void*)*3 + 2, v_suppressElabErrors_2820_);
lean_ctor_set_uint8(v___x_2823_, sizeof(void*)*3 + 3, v_isRecordingDeps_2821_);
v___x_2824_ = lean_st_ref_get(v___y_2814_);
v_traceState_2825_ = lean_ctor_get(v___x_2824_, 4);
lean_inc_ref(v_traceState_2825_);
lean_dec(v___x_2824_);
v_traces_2826_ = lean_ctor_get(v_traceState_2825_, 0);
lean_inc_ref(v_traces_2826_);
lean_dec_ref(v_traceState_2825_);
v___x_2827_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2826_);
lean_dec_ref(v_traces_2826_);
v_sz_2828_ = lean_array_size(v___x_2827_);
v___x_2829_ = ((size_t)0ULL);
v___x_2830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_2828_, v___x_2829_, v___x_2827_);
v_msg_2831_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2831_, 0, v_data_2808_);
lean_ctor_set(v_msg_2831_, 1, v_msg_2810_);
lean_ctor_set(v_msg_2831_, 2, v___x_2830_);
v___x_2832_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2831_, v___y_2811_, v___y_2812_, v___x_2823_, v___y_2814_);
lean_dec_ref_known(v___x_2823_, 3);
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2835_ = v___x_2832_;
v_isShared_2836_ = v_isSharedCheck_2871_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2871_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; lean_object* v_traceState_2838_; lean_object* v_env_2839_; lean_object* v_nextMacroScope_2840_; lean_object* v_ngen_2841_; lean_object* v_auxDeclNGen_2842_; lean_object* v_cache_2843_; lean_object* v_recordedDeps_2844_; lean_object* v_messages_2845_; lean_object* v_infoState_2846_; lean_object* v_snapshotTasks_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2870_; 
v___x_2837_ = lean_st_ref_take(v___y_2814_);
v_traceState_2838_ = lean_ctor_get(v___x_2837_, 4);
v_env_2839_ = lean_ctor_get(v___x_2837_, 0);
v_nextMacroScope_2840_ = lean_ctor_get(v___x_2837_, 1);
v_ngen_2841_ = lean_ctor_get(v___x_2837_, 2);
v_auxDeclNGen_2842_ = lean_ctor_get(v___x_2837_, 3);
v_cache_2843_ = lean_ctor_get(v___x_2837_, 5);
v_recordedDeps_2844_ = lean_ctor_get(v___x_2837_, 6);
v_messages_2845_ = lean_ctor_get(v___x_2837_, 7);
v_infoState_2846_ = lean_ctor_get(v___x_2837_, 8);
v_snapshotTasks_2847_ = lean_ctor_get(v___x_2837_, 9);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2849_ = v___x_2837_;
v_isShared_2850_ = v_isSharedCheck_2870_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_snapshotTasks_2847_);
lean_inc(v_infoState_2846_);
lean_inc(v_messages_2845_);
lean_inc(v_recordedDeps_2844_);
lean_inc(v_cache_2843_);
lean_inc(v_traceState_2838_);
lean_inc(v_auxDeclNGen_2842_);
lean_inc(v_ngen_2841_);
lean_inc(v_nextMacroScope_2840_);
lean_inc(v_env_2839_);
lean_dec(v___x_2837_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2870_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
uint64_t v_tid_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2868_; 
v_tid_2851_ = lean_ctor_get_uint64(v_traceState_2838_, sizeof(void*)*1);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_traceState_2838_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; 
v_unused_2869_ = lean_ctor_get(v_traceState_2838_, 0);
lean_dec(v_unused_2869_);
v___x_2853_ = v_traceState_2838_;
v_isShared_2854_ = v_isSharedCheck_2868_;
goto v_resetjp_2852_;
}
else
{
lean_dec(v_traceState_2838_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2868_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2855_ = lean_box(0);
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v_ref_2809_);
lean_ctor_set(v___x_2856_, 1, v_a_2833_);
v___x_2857_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2807_, v___x_2856_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2857_);
v___x_2859_ = v___x_2853_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2857_);
lean_ctor_set_uint64(v_reuseFailAlloc_2867_, sizeof(void*)*1, v_tid_2851_);
v___x_2859_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2861_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 4, v___x_2859_);
v___x_2861_ = v___x_2849_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_env_2839_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_nextMacroScope_2840_);
lean_ctor_set(v_reuseFailAlloc_2866_, 2, v_ngen_2841_);
lean_ctor_set(v_reuseFailAlloc_2866_, 3, v_auxDeclNGen_2842_);
lean_ctor_set(v_reuseFailAlloc_2866_, 4, v___x_2859_);
lean_ctor_set(v_reuseFailAlloc_2866_, 5, v_cache_2843_);
lean_ctor_set(v_reuseFailAlloc_2866_, 6, v_recordedDeps_2844_);
lean_ctor_set(v_reuseFailAlloc_2866_, 7, v_messages_2845_);
lean_ctor_set(v_reuseFailAlloc_2866_, 8, v_infoState_2846_);
lean_ctor_set(v_reuseFailAlloc_2866_, 9, v_snapshotTasks_2847_);
v___x_2861_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2862_ = lean_st_ref_put(v___y_2814_, v___x_2861_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2855_);
v___x_2864_ = v___x_2835_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2855_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_2807_ = stack[0].m_obj;
lean_object* v_data_2808_ = stack[1].m_obj;
lean_object* v_ref_2809_ = stack[2].m_obj;
lean_object* v_msg_2810_ = stack[3].m_obj;
lean_object* v___y_2811_ = stack[4].m_obj;
lean_object* v___y_2812_ = stack[5].m_obj;
lean_object* v___y_2813_ = stack[6].m_obj;
lean_object* v___y_2814_ = stack[7].m_obj;
lean_object* v_res_2872_;
v_res_2872_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2807_, v_data_2808_, v_ref_2809_, v_msg_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
stack->m_obj
 = v_res_2872_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_2873_, lean_object* v_data_2874_, lean_object* v_ref_2875_, lean_object* v_msg_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2873_, v_data_2874_, v_ref_2875_, v_msg_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
return v_res_2882_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_2885_ = l_Lean_stringToMessageData(v___x_2884_);
return v___x_2885_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2886_; double v___x_2887_; 
v___x_2886_ = lean_unsigned_to_nat(1000u);
v___x_2887_ = lean_float_of_nat(v___x_2886_);
return v___x_2887_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_2888_, uint8_t v_collapsed_2889_, lean_object* v_tag_2890_, lean_object* v_opts_2891_, uint8_t v_clsEnabled_2892_, lean_object* v_oldTraces_2893_, lean_object* v_msg_2894_, lean_object* v_resStartStop_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_fst_2906_; lean_object* v_snd_2907_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v_data_2911_; lean_object* v_fst_2922_; lean_object* v_snd_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; lean_object* v___y_2927_; lean_object* v_a_2928_; uint8_t v___y_2943_; double v___y_2975_; 
v_fst_2906_ = lean_ctor_get(v_resStartStop_2895_, 0);
lean_inc(v_fst_2906_);
v_snd_2907_ = lean_ctor_get(v_resStartStop_2895_, 1);
lean_inc(v_snd_2907_);
lean_dec_ref(v_resStartStop_2895_);
v_fst_2922_ = lean_ctor_get(v_snd_2907_, 0);
lean_inc(v_fst_2922_);
v_snd_2923_ = lean_ctor_get(v_snd_2907_, 1);
lean_inc(v_snd_2923_);
lean_dec(v_snd_2907_);
v___x_2924_ = l_Lean_trace_profiler;
v___x_2925_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2891_, v___x_2924_);
if (v___x_2925_ == 0)
{
v___y_2943_ = v___x_2925_;
goto v___jp_2942_;
}
else
{
lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2980_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2981_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2891_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2983_; double v___x_2984_; double v___x_2985_; double v___x_2986_; 
v___x_2982_ = l_Lean_trace_profiler_threshold;
v___x_2983_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2891_, v___x_2982_);
v___x_2984_ = lean_float_of_nat(v___x_2983_);
v___x_2985_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_2986_ = lean_float_div(v___x_2984_, v___x_2985_);
v___y_2975_ = v___x_2986_;
goto v___jp_2974_;
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2988_; double v___x_2989_; 
v___x_2987_ = l_Lean_trace_profiler_threshold;
v___x_2988_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2891_, v___x_2987_);
v___x_2989_ = lean_float_of_nat(v___x_2988_);
v___y_2975_ = v___x_2989_;
goto v___jp_2974_;
}
}
v___jp_2908_:
{
lean_object* v___x_2912_; 
lean_inc(v___y_2910_);
v___x_2912_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2893_, v_data_2911_, v___y_2910_, v___y_2909_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2913_; 
lean_dec_ref_known(v___x_2912_, 1);
v___x_2913_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2906_);
return v___x_2913_;
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v_fst_2906_);
v_a_2914_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2912_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2912_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
v___jp_2926_:
{
uint8_t v_result_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; double v___x_2932_; lean_object* v_data_2933_; 
v_result_2929_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_fst_2906_);
v___x_2930_ = lean_box(v_result_2929_);
v___x_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
v___x_2932_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2890_);
lean_inc_ref(v___x_2931_);
lean_inc(v_cls_2888_);
v_data_2933_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2933_, 0, v_cls_2888_);
lean_ctor_set(v_data_2933_, 1, v___x_2931_);
lean_ctor_set(v_data_2933_, 2, v_tag_2890_);
lean_ctor_set_float(v_data_2933_, sizeof(void*)*3, v___x_2932_);
lean_ctor_set_float(v_data_2933_, sizeof(void*)*3 + 8, v___x_2932_);
lean_ctor_set_uint8(v_data_2933_, sizeof(void*)*3 + 16, v_collapsed_2889_);
if (v___x_2925_ == 0)
{
lean_dec_ref_known(v___x_2931_, 1);
lean_dec(v_snd_2923_);
lean_dec(v_fst_2922_);
lean_dec_ref(v_tag_2890_);
lean_dec(v_cls_2888_);
v___y_2909_ = v_a_2928_;
v___y_2910_ = v___y_2927_;
v_data_2911_ = v_data_2933_;
goto v___jp_2908_;
}
else
{
lean_object* v_data_2934_; double v___x_2935_; double v___x_2936_; 
lean_dec_ref_known(v_data_2933_, 3);
v_data_2934_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2934_, 0, v_cls_2888_);
lean_ctor_set(v_data_2934_, 1, v___x_2931_);
lean_ctor_set(v_data_2934_, 2, v_tag_2890_);
v___x_2935_ = lean_unbox_float(v_fst_2922_);
lean_dec(v_fst_2922_);
lean_ctor_set_float(v_data_2934_, sizeof(void*)*3, v___x_2935_);
v___x_2936_ = lean_unbox_float(v_snd_2923_);
lean_dec(v_snd_2923_);
lean_ctor_set_float(v_data_2934_, sizeof(void*)*3 + 8, v___x_2936_);
lean_ctor_set_uint8(v_data_2934_, sizeof(void*)*3 + 16, v_collapsed_2889_);
v___y_2909_ = v_a_2928_;
v___y_2910_ = v___y_2927_;
v_data_2911_ = v_data_2934_;
goto v___jp_2908_;
}
}
v___jp_2937_:
{
lean_object* v_ref_2938_; lean_object* v___x_2939_; 
v_ref_2938_ = lean_ctor_get(v___y_2903_, 2);
lean_inc(v___y_2904_);
lean_inc_ref(v___y_2903_);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
lean_inc(v___y_2900_);
lean_inc_ref(v___y_2899_);
lean_inc(v___y_2898_);
lean_inc_ref(v___y_2897_);
lean_inc(v___y_2896_);
lean_inc(v_fst_2906_);
v___x_2939_ = lean_apply_11(v_msg_2894_, v_fst_2906_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, lean_box(0));
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v___y_2927_ = v_ref_2938_;
v_a_2928_ = v_a_2940_;
goto v___jp_2926_;
}
else
{
lean_object* v___x_2941_; 
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_2927_ = v_ref_2938_;
v_a_2928_ = v___x_2941_;
goto v___jp_2926_;
}
}
v___jp_2942_:
{
if (v_clsEnabled_2892_ == 0)
{
if (v___y_2943_ == 0)
{
lean_object* v___x_2944_; lean_object* v_traceState_2945_; lean_object* v_env_2946_; lean_object* v_nextMacroScope_2947_; lean_object* v_ngen_2948_; lean_object* v_auxDeclNGen_2949_; lean_object* v_cache_2950_; lean_object* v_recordedDeps_2951_; lean_object* v_messages_2952_; lean_object* v_infoState_2953_; lean_object* v_snapshotTasks_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v_snd_2923_);
lean_dec(v_fst_2922_);
lean_dec_ref(v_msg_2894_);
lean_dec_ref(v_tag_2890_);
lean_dec(v_cls_2888_);
v___x_2944_ = lean_st_ref_take(v___y_2904_);
v_traceState_2945_ = lean_ctor_get(v___x_2944_, 4);
v_env_2946_ = lean_ctor_get(v___x_2944_, 0);
v_nextMacroScope_2947_ = lean_ctor_get(v___x_2944_, 1);
v_ngen_2948_ = lean_ctor_get(v___x_2944_, 2);
v_auxDeclNGen_2949_ = lean_ctor_get(v___x_2944_, 3);
v_cache_2950_ = lean_ctor_get(v___x_2944_, 5);
v_recordedDeps_2951_ = lean_ctor_get(v___x_2944_, 6);
v_messages_2952_ = lean_ctor_get(v___x_2944_, 7);
v_infoState_2953_ = lean_ctor_get(v___x_2944_, 8);
v_snapshotTasks_2954_ = lean_ctor_get(v___x_2944_, 9);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2956_ = v___x_2944_;
v_isShared_2957_ = v_isSharedCheck_2973_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_snapshotTasks_2954_);
lean_inc(v_infoState_2953_);
lean_inc(v_messages_2952_);
lean_inc(v_recordedDeps_2951_);
lean_inc(v_cache_2950_);
lean_inc(v_traceState_2945_);
lean_inc(v_auxDeclNGen_2949_);
lean_inc(v_ngen_2948_);
lean_inc(v_nextMacroScope_2947_);
lean_inc(v_env_2946_);
lean_dec(v___x_2944_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2973_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
uint64_t v_tid_2958_; lean_object* v_traces_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2972_; 
v_tid_2958_ = lean_ctor_get_uint64(v_traceState_2945_, sizeof(void*)*1);
v_traces_2959_ = lean_ctor_get(v_traceState_2945_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_traceState_2945_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2961_ = v_traceState_2945_;
v_isShared_2962_ = v_isSharedCheck_2972_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_traces_2959_);
lean_dec(v_traceState_2945_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2972_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2963_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2893_, v_traces_2959_);
lean_dec_ref(v_traces_2959_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2963_);
v___x_2965_ = v___x_2961_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2963_);
lean_ctor_set_uint64(v_reuseFailAlloc_2971_, sizeof(void*)*1, v_tid_2958_);
v___x_2965_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2967_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 4, v___x_2965_);
v___x_2967_ = v___x_2956_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_env_2946_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_nextMacroScope_2947_);
lean_ctor_set(v_reuseFailAlloc_2970_, 2, v_ngen_2948_);
lean_ctor_set(v_reuseFailAlloc_2970_, 3, v_auxDeclNGen_2949_);
lean_ctor_set(v_reuseFailAlloc_2970_, 4, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2970_, 5, v_cache_2950_);
lean_ctor_set(v_reuseFailAlloc_2970_, 6, v_recordedDeps_2951_);
lean_ctor_set(v_reuseFailAlloc_2970_, 7, v_messages_2952_);
lean_ctor_set(v_reuseFailAlloc_2970_, 8, v_infoState_2953_);
lean_ctor_set(v_reuseFailAlloc_2970_, 9, v_snapshotTasks_2954_);
v___x_2967_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = lean_st_ref_put(v___y_2904_, v___x_2967_);
v___x_2969_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2906_);
return v___x_2969_;
}
}
}
}
}
else
{
goto v___jp_2937_;
}
}
else
{
goto v___jp_2937_;
}
}
v___jp_2974_:
{
double v___x_2976_; double v___x_2977_; double v___x_2978_; uint8_t v___x_2979_; 
v___x_2976_ = lean_unbox_float(v_snd_2923_);
v___x_2977_ = lean_unbox_float(v_fst_2922_);
v___x_2978_ = lean_float_sub(v___x_2976_, v___x_2977_);
v___x_2979_ = lean_float_decLt(v___y_2975_, v___x_2978_);
v___y_2943_ = v___x_2979_;
goto v___jp_2942_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2888_ = stack[0].m_obj;
uint8_t v_collapsed_2889_ = stack[1].m_num;
lean_object* v_tag_2890_ = stack[2].m_obj;
lean_object* v_opts_2891_ = stack[3].m_obj;
uint8_t v_clsEnabled_2892_ = stack[4].m_num;
lean_object* v_oldTraces_2893_ = stack[5].m_obj;
lean_object* v_msg_2894_ = stack[6].m_obj;
lean_object* v_resStartStop_2895_ = stack[7].m_obj;
lean_object* v___y_2896_ = stack[8].m_obj;
lean_object* v___y_2897_ = stack[9].m_obj;
lean_object* v___y_2898_ = stack[10].m_obj;
lean_object* v___y_2899_ = stack[11].m_obj;
lean_object* v___y_2900_ = stack[12].m_obj;
lean_object* v___y_2901_ = stack[13].m_obj;
lean_object* v___y_2902_ = stack[14].m_obj;
lean_object* v___y_2903_ = stack[15].m_obj;
lean_object* v___y_2904_ = stack[16].m_obj;
lean_object* v_res_2990_;
v_res_2990_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2888_, v_collapsed_2889_, v_tag_2890_, v_opts_2891_, v_clsEnabled_2892_, v_oldTraces_2893_, v_msg_2894_, v_resStartStop_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
stack->m_obj
 = v_res_2990_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object** _args){
lean_object* v_cls_2991_ = _args[0];
lean_object* v_collapsed_2992_ = _args[1];
lean_object* v_tag_2993_ = _args[2];
lean_object* v_opts_2994_ = _args[3];
lean_object* v_clsEnabled_2995_ = _args[4];
lean_object* v_oldTraces_2996_ = _args[5];
lean_object* v_msg_2997_ = _args[6];
lean_object* v_resStartStop_2998_ = _args[7];
lean_object* v___y_2999_ = _args[8];
lean_object* v___y_3000_ = _args[9];
lean_object* v___y_3001_ = _args[10];
lean_object* v___y_3002_ = _args[11];
lean_object* v___y_3003_ = _args[12];
lean_object* v___y_3004_ = _args[13];
lean_object* v___y_3005_ = _args[14];
lean_object* v___y_3006_ = _args[15];
lean_object* v___y_3007_ = _args[16];
lean_object* v___y_3008_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_3009_; uint8_t v_clsEnabled_boxed_3010_; lean_object* v_res_3011_; 
v_collapsed_boxed_3009_ = lean_unbox(v_collapsed_2992_);
v_clsEnabled_boxed_3010_ = lean_unbox(v_clsEnabled_2995_);
v_res_3011_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2991_, v_collapsed_boxed_3009_, v_tag_2993_, v_opts_2994_, v_clsEnabled_boxed_3010_, v_oldTraces_2996_, v_msg_2997_, v_resStartStop_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v_opts_2994_);
return v_res_3011_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3(void){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2));
v___x_3018_ = l_Lean_stringToMessageData(v___x_3017_);
return v___x_3018_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5(void){
_start:
{
lean_object* v___x_3020_; double v___x_3021_; 
v___x_3020_ = lean_unsigned_to_nat(1000000000u);
v___x_3021_ = lean_float_of_nat(v___x_3020_);
return v___x_3021_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object* v_P_3022_, lean_object* v_lhs_3023_, lean_object* v_rhs_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
uint8_t v___y_3036_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v_toCold_3058_; lean_object* v_options_3059_; lean_object* v_inheritedTraceOptions_3060_; uint8_t v_hasTrace_3061_; lean_object* v_cls_3062_; lean_object* v___f_3063_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; uint8_t v_____do__lift_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; 
v_toCold_3058_ = lean_ctor_get(v_a_3032_, 0);
v_options_3059_ = lean_ctor_get(v_toCold_3058_, 2);
v_inheritedTraceOptions_3060_ = lean_ctor_get(v_toCold_3058_, 11);
v_hasTrace_3061_ = lean_ctor_get_uint8(v_options_3059_, sizeof(void*)*1);
v_cls_3062_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_3063_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1));
if (v_hasTrace_3061_ == 0)
{
lean_object* v___x_3191_; lean_object* v_a_3192_; uint8_t v___x_3193_; 
v___x_3191_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3062_, v_inheritedTraceOptions_3060_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_a_3192_);
lean_dec_ref(v___x_3191_);
v___x_3193_ = lean_unbox(v_a_3192_);
lean_dec(v_a_3192_);
v_____do__lift_3168_ = v___x_3193_;
v___y_3169_ = v_a_3025_;
v___y_3170_ = v_a_3026_;
v___y_3171_ = v_a_3027_;
v___y_3172_ = v_a_3028_;
v___y_3173_ = v_a_3029_;
v___y_3174_ = v_a_3030_;
v___y_3175_ = v_a_3031_;
v___y_3176_ = v_a_3032_;
v___y_3177_ = v_a_3033_;
goto v___jp_3167_;
}
else
{
lean_object* v___f_3194_; uint8_t v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v_a_3202_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v_a_3214_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v_a_3232_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v_a_3247_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; 
v___f_3194_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4));
v___x_3195_ = 0;
v___x_3196_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3197_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3198_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3060_, v_options_3059_, v___x_3197_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3295_ = l_Lean_trace_profiler;
v___x_3296_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_3059_, v___x_3295_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; lean_object* v_a_3298_; uint8_t v___x_3299_; 
v___x_3297_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3062_, v_inheritedTraceOptions_3060_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref(v___x_3297_);
v___x_3299_ = lean_unbox(v_a_3298_);
lean_dec(v_a_3298_);
v_____do__lift_3168_ = v___x_3299_;
v___y_3169_ = v_a_3025_;
v___y_3170_ = v_a_3026_;
v___y_3171_ = v_a_3027_;
v___y_3172_ = v_a_3028_;
v___y_3173_ = v_a_3029_;
v___y_3174_ = v_a_3030_;
v___y_3175_ = v_a_3031_;
v___y_3176_ = v_a_3032_;
v___y_3177_ = v_a_3033_;
goto v___jp_3167_;
}
else
{
goto v___jp_3262_;
}
}
else
{
goto v___jp_3262_;
}
v___jp_3199_:
{
lean_object* v___x_3203_; double v___x_3204_; double v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3203_ = lean_io_get_num_heartbeats();
v___x_3204_ = lean_float_of_nat(v___y_3201_);
v___x_3205_ = lean_float_of_nat(v___x_3203_);
v___x_3206_ = lean_box_float(v___x_3204_);
v___x_3207_ = lean_box_float(v___x_3205_);
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3206_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3209_, 0, v_a_3202_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3062_, v___x_3195_, v___x_3196_, v_options_3059_, v___x_3198_, v___y_3200_, v___f_3194_, v___x_3209_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
return v___x_3210_;
}
v___jp_3211_:
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v_a_3214_);
v___y_3200_ = v___y_3212_;
v___y_3201_ = v___y_3213_;
v_a_3202_ = v___x_3215_;
goto v___jp_3199_;
}
v___jp_3216_:
{
if (lean_obj_tag(v___y_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
v_a_3220_ = lean_ctor_get(v___y_3219_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___y_3219_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___y_3219_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___y_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
lean_ctor_set_tag(v___x_3222_, 1);
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
v___y_3200_ = v___y_3217_;
v___y_3201_ = v___y_3218_;
v_a_3202_ = v___x_3225_;
goto v___jp_3199_;
}
}
}
else
{
lean_object* v_a_3228_; 
v_a_3228_ = lean_ctor_get(v___y_3219_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___y_3219_, 1);
v___y_3212_ = v___y_3217_;
v___y_3213_ = v___y_3218_;
v_a_3214_ = v_a_3228_;
goto v___jp_3211_;
}
}
v___jp_3229_:
{
lean_object* v___x_3233_; double v___x_3234_; double v___x_3235_; double v___x_3236_; double v___x_3237_; double v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3233_ = lean_io_mono_nanos_now();
v___x_3234_ = lean_float_of_nat(v___y_3230_);
v___x_3235_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__5);
v___x_3236_ = lean_float_div(v___x_3234_, v___x_3235_);
v___x_3237_ = lean_float_of_nat(v___x_3233_);
v___x_3238_ = lean_float_div(v___x_3237_, v___x_3235_);
v___x_3239_ = lean_box_float(v___x_3236_);
v___x_3240_ = lean_box_float(v___x_3238_);
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3239_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v_a_3232_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_3062_, v___x_3195_, v___x_3196_, v_options_3059_, v___x_3198_, v___y_3231_, v___f_3194_, v___x_3242_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
return v___x_3243_;
}
v___jp_3244_:
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3248_, 0, v_a_3247_);
v___y_3230_ = v___y_3245_;
v___y_3231_ = v___y_3246_;
v_a_3232_ = v___x_3248_;
goto v___jp_3229_;
}
v___jp_3249_:
{
if (lean_obj_tag(v___y_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
v_a_3253_ = lean_ctor_get(v___y_3252_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___y_3252_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___y_3252_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___y_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set_tag(v___x_3255_, 1);
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
v___y_3230_ = v___y_3250_;
v___y_3231_ = v___y_3251_;
v_a_3232_ = v___x_3258_;
goto v___jp_3229_;
}
}
}
else
{
lean_object* v_a_3261_; 
v_a_3261_ = lean_ctor_get(v___y_3252_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___y_3252_, 1);
v___y_3245_ = v___y_3250_;
v___y_3246_ = v___y_3251_;
v_a_3247_ = v_a_3261_;
goto v___jp_3244_;
}
}
v___jp_3262_:
{
lean_object* v___x_3263_; lean_object* v_a_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v___x_3263_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_3033_);
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref(v___x_3263_);
v___x_3265_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3266_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_3059_, v___x_3265_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v_a_3269_; uint8_t v___x_3270_; 
v___x_3267_ = lean_io_mono_nanos_now();
v___x_3268_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3062_, v_inheritedTraceOptions_3060_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref(v___x_3268_);
v___x_3270_ = lean_unbox(v_a_3269_);
lean_dec(v_a_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = lean_box(0);
v___x_3272_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_3023_, v_rhs_3024_, v___x_3266_, v___f_3063_, v_cls_3062_, v_P_3022_, v___x_3271_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
v___y_3250_ = v___x_3267_;
v___y_3251_ = v_a_3264_;
v___y_3252_ = v___x_3272_;
goto v___jp_3249_;
}
else
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3273_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_3024_);
lean_inc_ref(v_lhs_3023_);
lean_inc_ref(v_P_3022_);
v___x_3274_ = l_Lean_mkAppB(v_P_3022_, v_lhs_3023_, v_rhs_3024_);
v___x_3275_ = l_Lean_indentExpr(v___x_3274_);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3273_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3062_, v___x_3276_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3279_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v___x_3279_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_3023_, v_rhs_3024_, v___x_3266_, v___f_3063_, v_cls_3062_, v_P_3022_, v_a_3278_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
v___y_3250_ = v___x_3267_;
v___y_3251_ = v_a_3264_;
v___y_3252_ = v___x_3279_;
goto v___jp_3249_;
}
else
{
lean_object* v_a_3280_; 
lean_dec_ref(v_rhs_3024_);
lean_dec_ref(v_lhs_3023_);
lean_dec_ref(v_P_3022_);
v_a_3280_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3277_, 1);
v___y_3245_ = v___x_3267_;
v___y_3246_ = v_a_3264_;
v_a_3247_ = v_a_3280_;
goto v___jp_3244_;
}
}
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v_a_3283_; uint8_t v___x_3284_; 
v___x_3281_ = lean_io_get_num_heartbeats();
v___x_3282_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3062_, v_inheritedTraceOptions_3060_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref(v___x_3282_);
v___x_3284_ = lean_unbox(v_a_3283_);
lean_dec(v_a_3283_);
if (v___x_3284_ == 0)
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = lean_box(0);
v___x_3286_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_3023_, v_rhs_3024_, v_P_3022_, v_cls_3062_, v___x_3266_, v___f_3063_, v___x_3195_, v___x_3285_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
v___y_3217_ = v_a_3264_;
v___y_3218_ = v___x_3281_;
v___y_3219_ = v___x_3286_;
goto v___jp_3216_;
}
else
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3287_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_3024_);
lean_inc_ref(v_lhs_3023_);
lean_inc_ref(v_P_3022_);
v___x_3288_ = l_Lean_mkAppB(v_P_3022_, v_lhs_3023_, v_rhs_3024_);
v___x_3289_ = l_Lean_indentExpr(v___x_3288_);
v___x_3290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3287_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3062_, v___x_3290_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3293_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v___x_3291_, 1);
v___x_3293_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__4(v_lhs_3023_, v_rhs_3024_, v_P_3022_, v_cls_3062_, v___x_3266_, v___f_3063_, v___x_3195_, v_a_3292_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
v___y_3217_ = v_a_3264_;
v___y_3218_ = v___x_3281_;
v___y_3219_ = v___x_3293_;
goto v___jp_3216_;
}
else
{
lean_object* v_a_3294_; 
lean_dec_ref(v_rhs_3024_);
lean_dec_ref(v_lhs_3023_);
lean_dec_ref(v_P_3022_);
v_a_3294_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3294_);
lean_dec_ref_known(v___x_3291_, 1);
v___y_3212_ = v_a_3264_;
v___y_3213_ = v___x_3281_;
v_a_3214_ = v_a_3294_;
goto v___jp_3211_;
}
}
}
}
}
v___jp_3035_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3037_, 0, v___y_3036_);
lean_ctor_set_uint8(v___x_3037_, 1, v___y_3036_);
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
return v___x_3038_;
}
v___jp_3039_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
return v___x_3041_;
}
v___jp_3042_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
return v___x_3044_;
}
v___jp_3045_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3054_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_3055_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8));
v___x_3056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3056_, 0, v___y_3047_);
lean_ctor_set(v___x_3056_, 1, v___x_3054_);
lean_ctor_set(v___x_3056_, 2, v___x_3055_);
v___x_3057_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_3046_, v___x_3056_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
return v___x_3057_;
}
v___jp_3064_:
{
lean_object* v___x_3074_; 
lean_inc_ref(v_lhs_3023_);
v___x_3074_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_3023_);
if (lean_obj_tag(v___x_3074_) == 1)
{
lean_object* v_val_3075_; lean_object* v___x_3076_; 
v_val_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_val_3075_);
lean_dec_ref_known(v___x_3074_, 1);
lean_inc_ref(v_rhs_3024_);
v___x_3076_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_3024_);
if (lean_obj_tag(v___x_3076_) == 1)
{
lean_object* v_val_3077_; uint8_t v___x_3078_; 
v_val_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_val_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___x_3078_ = lean_expr_eqv(v_val_3075_, v_val_3077_);
if (v___x_3078_ == 0)
{
lean_object* v_toCold_3079_; lean_object* v_inheritedTraceOptions_3080_; lean_object* v___x_3081_; lean_object* v_a_3082_; uint8_t v___x_3083_; 
lean_dec_ref(v_P_3022_);
v_toCold_3079_ = lean_ctor_get(v___y_3072_, 0);
v_inheritedTraceOptions_3080_ = lean_ctor_get(v_toCold_3079_, 11);
v___x_3081_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3062_, v_inheritedTraceOptions_3080_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref(v___x_3081_);
v___x_3083_ = lean_unbox(v_a_3082_);
lean_dec(v_a_3082_);
if (v___x_3083_ == 0)
{
lean_dec(v_val_3077_);
lean_dec(v_val_3075_);
lean_dec_ref(v_rhs_3024_);
lean_dec_ref(v_lhs_3023_);
v___y_3036_ = v___x_3078_;
goto v___jp_3035_;
}
else
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3084_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1);
v___x_3085_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3075_);
v___x_3086_ = l_Lean_MessageData_ofExpr(v___x_3085_);
v___x_3087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3084_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3);
v___x_3089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3087_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = l_Lean_indentExpr(v_lhs_3023_);
v___x_3091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5);
v___x_3093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3091_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3077_);
v___x_3095_ = l_Lean_MessageData_ofExpr(v___x_3094_);
v___x_3096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3093_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
lean_ctor_set(v___x_3097_, 1, v___x_3088_);
v___x_3098_ = l_Lean_indentExpr(v_rhs_3024_);
v___x_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3062_, v___x_3099_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_dec_ref_known(v___x_3100_, 1);
v___y_3036_ = v___x_3078_;
goto v___jp_3035_;
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
else
{
lean_object* v_toCold_3109_; lean_object* v_options_3110_; lean_object* v_inheritedTraceOptions_3111_; uint8_t v_hasTrace_3112_; uint8_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___f_3115_; 
lean_dec(v_val_3077_);
v_toCold_3109_ = lean_ctor_get(v___y_3072_, 0);
v_options_3110_ = lean_ctor_get(v_toCold_3109_, 2);
v_inheritedTraceOptions_3111_ = lean_ctor_get(v_toCold_3109_, 11);
v_hasTrace_3112_ = lean_ctor_get_uint8(v_options_3110_, sizeof(void*)*1);
v___x_3113_ = 0;
v___x_3114_ = lean_box(v___x_3113_);
lean_inc(v_val_3075_);
v___f_3115_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_3115_, 0, v_val_3075_);
lean_closure_set(v___f_3115_, 1, v_lhs_3023_);
lean_closure_set(v___f_3115_, 2, v_rhs_3024_);
lean_closure_set(v___f_3115_, 3, v_P_3022_);
lean_closure_set(v___f_3115_, 4, v___x_3114_);
if (v_hasTrace_3112_ == 0)
{
v___y_3046_ = v___f_3115_;
v___y_3047_ = v_val_3075_;
v___y_3048_ = v___y_3068_;
v___y_3049_ = v___y_3069_;
v___y_3050_ = v___y_3070_;
v___y_3051_ = v___y_3071_;
v___y_3052_ = v___y_3072_;
v___y_3053_ = v___y_3073_;
goto v___jp_3045_;
}
else
{
lean_object* v___x_3116_; uint8_t v___x_3117_; 
v___x_3116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3117_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3111_, v_options_3110_, v___x_3116_);
if (v___x_3117_ == 0)
{
v___y_3046_ = v___f_3115_;
v___y_3047_ = v_val_3075_;
v___y_3048_ = v___y_3068_;
v___y_3049_ = v___y_3069_;
v___y_3050_ = v___y_3070_;
v___y_3051_ = v___y_3071_;
v___y_3052_ = v___y_3072_;
v___y_3053_ = v___y_3073_;
goto v___jp_3045_;
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3118_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10);
lean_inc(v_val_3075_);
v___x_3119_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_3075_);
v___x_3120_ = l_Lean_MessageData_ofExpr(v___x_3119_);
v___x_3121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3118_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3062_, v___x_3123_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_dec_ref_known(v___x_3124_, 1);
v___y_3046_ = v___f_3115_;
v___y_3047_ = v_val_3075_;
v___y_3048_ = v___y_3068_;
v___y_3049_ = v___y_3069_;
v___y_3050_ = v___y_3070_;
v___y_3051_ = v___y_3071_;
v___y_3052_ = v___y_3072_;
v___y_3053_ = v___y_3073_;
goto v___jp_3045_;
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec_ref(v___f_3115_);
lean_dec(v_val_3075_);
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3124_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3124_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_3133_; lean_object* v_inheritedTraceOptions_3134_; lean_object* v___x_3135_; lean_object* v_a_3136_; uint8_t v___x_3137_; 
lean_dec(v___x_3076_);
lean_dec(v_val_3075_);
lean_dec_ref(v_lhs_3023_);
lean_dec_ref(v_P_3022_);
v_toCold_3133_ = lean_ctor_get(v___y_3072_, 0);
v_inheritedTraceOptions_3134_ = lean_ctor_get(v_toCold_3133_, 11);
v___x_3135_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3062_, v_inheritedTraceOptions_3134_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref(v___x_3135_);
v___x_3137_ = lean_unbox(v_a_3136_);
lean_dec(v_a_3136_);
if (v___x_3137_ == 0)
{
lean_dec_ref(v_rhs_3024_);
goto v___jp_3042_;
}
else
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3138_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_3139_ = l_Lean_indentExpr(v_rhs_3024_);
v___x_3140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3138_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3062_, v___x_3140_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_dec_ref_known(v___x_3141_, 1);
goto v___jp_3042_;
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_3150_; lean_object* v_inheritedTraceOptions_3151_; lean_object* v___x_3152_; lean_object* v_a_3153_; uint8_t v___x_3154_; 
lean_dec(v___x_3074_);
lean_dec_ref(v_rhs_3024_);
lean_dec_ref(v_P_3022_);
v_toCold_3150_ = lean_ctor_get(v___y_3072_, 0);
v_inheritedTraceOptions_3151_ = lean_ctor_get(v_toCold_3150_, 11);
v___x_3152_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_3062_, v_inheritedTraceOptions_3151_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref(v___x_3152_);
v___x_3154_ = lean_unbox(v_a_3153_);
lean_dec(v_a_3153_);
if (v___x_3154_ == 0)
{
lean_dec_ref(v_lhs_3023_);
goto v___jp_3039_;
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3155_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14);
v___x_3156_ = l_Lean_indentExpr(v_lhs_3023_);
v___x_3157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3155_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3062_, v___x_3157_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_dec_ref_known(v___x_3158_, 1);
goto v___jp_3039_;
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
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
v___jp_3167_:
{
if (v_____do__lift_3168_ == 0)
{
v___y_3065_ = v___y_3169_;
v___y_3066_ = v___y_3170_;
v___y_3067_ = v___y_3171_;
v___y_3068_ = v___y_3172_;
v___y_3069_ = v___y_3173_;
v___y_3070_ = v___y_3174_;
v___y_3071_ = v___y_3175_;
v___y_3072_ = v___y_3176_;
v___y_3073_ = v___y_3177_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3178_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3);
lean_inc_ref(v_rhs_3024_);
lean_inc_ref(v_lhs_3023_);
lean_inc_ref(v_P_3022_);
v___x_3179_ = l_Lean_mkAppB(v_P_3022_, v_lhs_3023_, v_rhs_3024_);
v___x_3180_ = l_Lean_indentExpr(v___x_3179_);
v___x_3181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3178_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3062_, v___x_3181_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_dec_ref_known(v___x_3182_, 1);
v___y_3065_ = v___y_3169_;
v___y_3066_ = v___y_3170_;
v___y_3067_ = v___y_3171_;
v___y_3068_ = v___y_3172_;
v___y_3069_ = v___y_3173_;
v___y_3070_ = v___y_3174_;
v___y_3071_ = v___y_3175_;
v___y_3072_ = v___y_3176_;
v___y_3073_ = v___y_3177_;
goto v___jp_3064_;
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec_ref(v_rhs_3024_);
lean_dec_ref(v_lhs_3023_);
lean_dec_ref(v_P_3022_);
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3182_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3182_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_0interp(lean_interpreter_value* stack)
{
lean_object* v_P_3022_ = stack[0].m_obj;
lean_object* v_lhs_3023_ = stack[1].m_obj;
lean_object* v_rhs_3024_ = stack[2].m_obj;
lean_object* v_a_3025_ = stack[3].m_obj;
lean_object* v_a_3026_ = stack[4].m_obj;
lean_object* v_a_3027_ = stack[5].m_obj;
lean_object* v_a_3028_ = stack[6].m_obj;
lean_object* v_a_3029_ = stack[7].m_obj;
lean_object* v_a_3030_ = stack[8].m_obj;
lean_object* v_a_3031_ = stack[9].m_obj;
lean_object* v_a_3032_ = stack[10].m_obj;
lean_object* v_a_3033_ = stack[11].m_obj;
lean_object* v_res_3300_;
v_res_3300_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v_P_3022_, v_lhs_3023_, v_rhs_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
stack->m_obj
 = v_res_3300_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3301_, lean_object* v_lhs_3302_, lean_object* v_rhs_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v_P_3301_, v_lhs_3302_, v_rhs_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
lean_dec(v_a_3308_);
lean_dec_ref(v_a_3307_);
lean_dec(v_a_3306_);
lean_dec_ref(v_a_3305_);
lean_dec(v_a_3304_);
return v_res_3314_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3315_, lean_object* v_msg_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3315_, v_msg_3316_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
return v___x_3327_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3315_ = stack[0].m_obj;
lean_object* v_msg_3316_ = stack[1].m_obj;
lean_object* v___y_3317_ = stack[2].m_obj;
lean_object* v___y_3318_ = stack[3].m_obj;
lean_object* v___y_3319_ = stack[4].m_obj;
lean_object* v___y_3320_ = stack[5].m_obj;
lean_object* v___y_3321_ = stack[6].m_obj;
lean_object* v___y_3322_ = stack[7].m_obj;
lean_object* v___y_3323_ = stack[8].m_obj;
lean_object* v___y_3324_ = stack[9].m_obj;
lean_object* v___y_3325_ = stack[10].m_obj;
lean_object* v_res_3328_;
v_res_3328_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(v_cls_3315_, v_msg_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
stack->m_obj
 = v_res_3328_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3329_, lean_object* v_msg_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(v_cls_3329_, v_msg_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
return v_res_3341_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_00_u03b1_3342_, lean_object* v_x_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_3343_);
return v___x_3354_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3343_ = stack[1].m_obj;
lean_object* v___y_3344_ = stack[2].m_obj;
lean_object* v___y_3345_ = stack[3].m_obj;
lean_object* v___y_3346_ = stack[4].m_obj;
lean_object* v___y_3347_ = stack[5].m_obj;
lean_object* v___y_3348_ = stack[6].m_obj;
lean_object* v___y_3349_ = stack[7].m_obj;
lean_object* v___y_3350_ = stack[8].m_obj;
lean_object* v___y_3351_ = stack[9].m_obj;
lean_object* v___y_3352_ = stack[10].m_obj;
lean_object* v_res_3355_;
v_res_3355_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_box(0), v_x_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
stack->m_obj
 = v_res_3355_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3356_, lean_object* v_x_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_00_u03b1_3356_, v_x_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
return v_res_3368_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_oldTraces_3369_, lean_object* v_data_3370_, lean_object* v_ref_3371_, lean_object* v_msg_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3369_, v_data_3370_, v_ref_3371_, v_msg_3372_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
return v___x_3383_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_3369_ = stack[0].m_obj;
lean_object* v_data_3370_ = stack[1].m_obj;
lean_object* v_ref_3371_ = stack[2].m_obj;
lean_object* v_msg_3372_ = stack[3].m_obj;
lean_object* v___y_3373_ = stack[4].m_obj;
lean_object* v___y_3374_ = stack[5].m_obj;
lean_object* v___y_3375_ = stack[6].m_obj;
lean_object* v___y_3376_ = stack[7].m_obj;
lean_object* v___y_3377_ = stack[8].m_obj;
lean_object* v___y_3378_ = stack[9].m_obj;
lean_object* v___y_3379_ = stack[10].m_obj;
lean_object* v___y_3380_ = stack[11].m_obj;
lean_object* v___y_3381_ = stack[12].m_obj;
lean_object* v_res_3384_;
v_res_3384_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_oldTraces_3369_, v_data_3370_, v_ref_3371_, v_msg_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
stack->m_obj
 = v_res_3384_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_oldTraces_3385_, lean_object* v_data_3386_, lean_object* v_ref_3387_, lean_object* v_msg_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_oldTraces_3385_, v_data_3386_, v_ref_3387_, v_msg_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
return v_res_3399_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(lean_object* v_x_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
return v___x_3412_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3400_ = stack[0].m_obj;
lean_object* v___y_3401_ = stack[1].m_obj;
lean_object* v___y_3402_ = stack[2].m_obj;
lean_object* v___y_3403_ = stack[3].m_obj;
lean_object* v___y_3404_ = stack[4].m_obj;
lean_object* v___y_3405_ = stack[5].m_obj;
lean_object* v___y_3406_ = stack[6].m_obj;
lean_object* v___y_3407_ = stack[7].m_obj;
lean_object* v___y_3408_ = stack[8].m_obj;
lean_object* v___y_3409_ = stack[9].m_obj;
lean_object* v_res_3413_;
v_res_3413_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v_x_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
stack->m_obj
 = v_res_3413_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0___boxed(lean_object* v_x_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v_x_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
return v_res_3425_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(lean_object* v_arg_3431_, lean_object* v_arg_3432_, lean_object* v_arg_3433_, lean_object* v_arg_3434_, lean_object* v_____r_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___x_3446_; 
lean_inc_ref(v_arg_3431_);
v___x_3446_ = l_Lean_Meta_getDecLevel(v_arg_3431_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
v___x_3448_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3449_ = lean_box(0);
v___x_3450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3450_, 0, v_a_3447_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = l_Lean_Expr_const___override(v___x_3448_, v___x_3450_);
v___x_3452_ = l_Lean_mkAppB(v___x_3451_, v_arg_3431_, v_arg_3432_);
v___x_3453_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3452_, v_arg_3433_, v_arg_3434_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
return v___x_3453_;
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_dec_ref(v_arg_3434_);
lean_dec_ref(v_arg_3433_);
lean_dec_ref(v_arg_3432_);
lean_dec_ref(v_arg_3431_);
v_a_3454_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3446_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3446_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_3431_ = stack[0].m_obj;
lean_object* v_arg_3432_ = stack[1].m_obj;
lean_object* v_arg_3433_ = stack[2].m_obj;
lean_object* v_arg_3434_ = stack[3].m_obj;
lean_object* v_____r_3435_ = stack[4].m_obj;
lean_object* v___y_3436_ = stack[5].m_obj;
lean_object* v___y_3437_ = stack[6].m_obj;
lean_object* v___y_3438_ = stack[7].m_obj;
lean_object* v___y_3439_ = stack[8].m_obj;
lean_object* v___y_3440_ = stack[9].m_obj;
lean_object* v___y_3441_ = stack[10].m_obj;
lean_object* v___y_3442_ = stack[11].m_obj;
lean_object* v___y_3443_ = stack[12].m_obj;
lean_object* v___y_3444_ = stack[13].m_obj;
lean_object* v_res_3462_;
v_res_3462_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3431_, v_arg_3432_, v_arg_3433_, v_arg_3434_, v_____r_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
stack->m_obj
 = v_res_3462_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___boxed(lean_object* v_arg_3463_, lean_object* v_arg_3464_, lean_object* v_arg_3465_, lean_object* v_arg_3466_, lean_object* v_____r_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3463_, v_arg_3464_, v_arg_3465_, v_arg_3466_, v_____r_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
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
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(lean_object* v_arg_3482_, lean_object* v_arg_3483_, lean_object* v_arg_3484_, lean_object* v_____r_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v___x_3496_; 
lean_inc_ref(v_arg_3482_);
v___x_3496_ = l_Lean_Meta_getLevel(v_arg_3482_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
v___x_3498_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3499_ = lean_box(0);
v___x_3500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3500_, 0, v_a_3497_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
v___x_3501_ = l_Lean_Expr_const___override(v___x_3498_, v___x_3500_);
v___x_3502_ = l_Lean_Expr_app___override(v___x_3501_, v_arg_3482_);
v___x_3503_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3502_, v_arg_3483_, v_arg_3484_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
return v___x_3503_;
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec_ref(v_arg_3484_);
lean_dec_ref(v_arg_3483_);
lean_dec_ref(v_arg_3482_);
v_a_3504_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3496_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3496_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_3482_ = stack[0].m_obj;
lean_object* v_arg_3483_ = stack[1].m_obj;
lean_object* v_arg_3484_ = stack[2].m_obj;
lean_object* v_____r_3485_ = stack[3].m_obj;
lean_object* v___y_3486_ = stack[4].m_obj;
lean_object* v___y_3487_ = stack[5].m_obj;
lean_object* v___y_3488_ = stack[6].m_obj;
lean_object* v___y_3489_ = stack[7].m_obj;
lean_object* v___y_3490_ = stack[8].m_obj;
lean_object* v___y_3491_ = stack[9].m_obj;
lean_object* v___y_3492_ = stack[10].m_obj;
lean_object* v___y_3493_ = stack[11].m_obj;
lean_object* v___y_3494_ = stack[12].m_obj;
lean_object* v_res_3512_;
v_res_3512_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3482_, v_arg_3483_, v_arg_3484_, v_____r_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
stack->m_obj
 = v_res_3512_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___boxed(lean_object* v_arg_3513_, lean_object* v_arg_3514_, lean_object* v_arg_3515_, lean_object* v_____r_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3513_, v_arg_3514_, v_arg_3515_, v_____r_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
return v_res_3527_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0));
v___x_3530_ = l_Lean_stringToMessageData(v___x_3529_);
return v___x_3530_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = l_Lean_checkEmoji;
v___x_3532_ = l_Lean_stringToMessageData(v___x_3531_);
return v___x_3532_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3533_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2);
v___x_3534_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
lean_ctor_set(v___x_3535_, 1, v___x_3533_);
return v___x_3535_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4));
v___x_3538_ = l_Lean_stringToMessageData(v___x_3537_);
return v___x_3538_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5);
v___x_3540_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
lean_ctor_set(v___x_3541_, 1, v___x_3539_);
return v___x_3541_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7));
v___x_3544_ = l_Lean_stringToMessageData(v___x_3543_);
return v___x_3544_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9(void){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3545_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3546_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3);
v___x_3547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
lean_ctor_set(v___x_3547_, 1, v___x_3545_);
return v___x_3547_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object* v_e_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v___y_3560_; lean_object* v___x_3592_; 
v___x_3592_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3548_, v_a_3555_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref_known(v___x_3592_, 1);
v___x_3594_ = l_Lean_Expr_cleanupAnnotations(v_a_3593_);
v___x_3595_ = l_Lean_Expr_isApp(v___x_3594_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
lean_dec_ref(v___x_3594_);
v___x_3596_ = lean_box(0);
v___x_3597_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3596_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
v___y_3560_ = v___x_3597_;
goto v___jp_3559_;
}
else
{
lean_object* v_arg_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; 
v_arg_3598_ = lean_ctor_get(v___x_3594_, 1);
lean_inc_ref(v_arg_3598_);
v___x_3599_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3594_);
v___x_3600_ = l_Lean_Expr_isApp(v___x_3599_);
if (v___x_3600_ == 0)
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
lean_dec_ref(v___x_3599_);
lean_dec_ref(v_arg_3598_);
v___x_3601_ = lean_box(0);
v___x_3602_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3601_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
v___y_3560_ = v___x_3602_;
goto v___jp_3559_;
}
else
{
lean_object* v_arg_3603_; lean_object* v___x_3604_; uint8_t v___x_3605_; 
v_arg_3603_ = lean_ctor_get(v___x_3599_, 1);
lean_inc_ref(v_arg_3603_);
v___x_3604_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3599_);
v___x_3605_ = l_Lean_Expr_isApp(v___x_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
lean_dec_ref(v___x_3604_);
lean_dec_ref(v_arg_3603_);
lean_dec_ref(v_arg_3598_);
v___x_3606_ = lean_box(0);
v___x_3607_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3606_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
v___y_3560_ = v___x_3607_;
goto v___jp_3559_;
}
else
{
lean_object* v_arg_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
v_arg_3608_ = lean_ctor_get(v___x_3604_, 1);
lean_inc_ref(v_arg_3608_);
v___x_3609_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3604_);
v___x_3610_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3611_ = l_Lean_Expr_isConstOf(v___x_3609_, v___x_3610_);
if (v___x_3611_ == 0)
{
uint8_t v___x_3612_; 
v___x_3612_ = l_Lean_Expr_isApp(v___x_3609_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
lean_dec_ref(v___x_3609_);
lean_dec_ref(v_arg_3608_);
lean_dec_ref(v_arg_3603_);
lean_dec_ref(v_arg_3598_);
v___x_3613_ = lean_box(0);
v___x_3614_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3613_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
v___y_3560_ = v___x_3614_;
goto v___jp_3559_;
}
else
{
lean_object* v_arg_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
v_arg_3615_ = lean_ctor_get(v___x_3609_, 1);
lean_inc_ref(v_arg_3615_);
v___x_3616_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3609_);
v___x_3617_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___closed__2));
v___x_3618_ = l_Lean_Expr_isConstOf(v___x_3616_, v___x_3617_);
lean_dec_ref(v___x_3616_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
lean_dec_ref(v_arg_3615_);
lean_dec_ref(v_arg_3608_);
lean_dec_ref(v_arg_3603_);
lean_dec_ref(v_arg_3598_);
v___x_3619_ = lean_box(0);
v___x_3620_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3619_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
v___y_3560_ = v___x_3620_;
goto v___jp_3559_;
}
else
{
lean_object* v_toCold_3621_; lean_object* v_options_3622_; lean_object* v_inheritedTraceOptions_3623_; uint8_t v_hasTrace_3624_; 
v_toCold_3621_ = lean_ctor_get(v_a_3556_, 0);
v_options_3622_ = lean_ctor_get(v_toCold_3621_, 2);
v_inheritedTraceOptions_3623_ = lean_ctor_get(v_toCold_3621_, 11);
v_hasTrace_3624_ = lean_ctor_get_uint8(v_options_3622_, sizeof(void*)*1);
if (v_hasTrace_3624_ == 0)
{
goto v___jp_3625_;
}
else
{
lean_object* v___x_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; 
v___x_3628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3629_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3630_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3623_, v_options_3622_, v___x_3629_);
if (v___x_3630_ == 0)
{
goto v___jp_3625_;
}
else
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6);
v___x_3632_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3628_, v___x_3631_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3634_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3633_);
lean_dec_ref_known(v___x_3632_, 1);
v___x_3634_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3615_, v_arg_3608_, v_arg_3603_, v_arg_3598_, v_a_3633_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
v___y_3560_ = v___x_3634_;
goto v___jp_3559_;
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_dec_ref(v_arg_3615_);
lean_dec_ref(v_arg_3608_);
lean_dec_ref(v_arg_3603_);
lean_dec_ref(v_arg_3598_);
v_a_3635_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3632_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3632_);
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
v___jp_3625_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = lean_box(0);
v___x_3627_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3615_, v_arg_3608_, v_arg_3603_, v_arg_3598_, v___x_3626_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
v___y_3560_ = v___x_3627_;
goto v___jp_3559_;
}
}
}
}
else
{
lean_object* v_toCold_3643_; lean_object* v_options_3644_; lean_object* v_inheritedTraceOptions_3645_; uint8_t v_hasTrace_3646_; 
lean_dec_ref(v___x_3609_);
v_toCold_3643_ = lean_ctor_get(v_a_3556_, 0);
v_options_3644_ = lean_ctor_get(v_toCold_3643_, 2);
v_inheritedTraceOptions_3645_ = lean_ctor_get(v_toCold_3643_, 11);
v_hasTrace_3646_ = lean_ctor_get_uint8(v_options_3644_, sizeof(void*)*1);
if (v_hasTrace_3646_ == 0)
{
goto v___jp_3647_;
}
else
{
lean_object* v___x_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; 
v___x_3650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3651_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3652_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3645_, v_options_3644_, v___x_3651_);
if (v___x_3652_ == 0)
{
goto v___jp_3647_;
}
else
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9);
v___x_3654_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3650_, v___x_3653_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3656_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___x_3654_, 1);
v___x_3656_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3608_, v_arg_3603_, v_arg_3598_, v_a_3655_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
v___y_3560_ = v___x_3656_;
goto v___jp_3559_;
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_dec_ref(v_arg_3608_);
lean_dec_ref(v_arg_3603_);
lean_dec_ref(v_arg_3598_);
v_a_3657_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3654_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3654_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
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
v___jp_3647_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = lean_box(0);
v___x_3649_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3608_, v_arg_3603_, v_arg_3598_, v___x_3648_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
v___y_3560_ = v___x_3649_;
goto v___jp_3559_;
}
}
}
}
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
v_a_3665_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3592_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3592_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
v___jp_3559_:
{
if (lean_obj_tag(v___y_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3591_; 
v_a_3561_ = lean_ctor_get(v___y_3560_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___y_3560_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3563_ = v___y_3560_;
v_isShared_3564_ = v_isSharedCheck_3591_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___y_3560_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3591_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
if (lean_obj_tag(v_a_3561_) == 0)
{
uint8_t v_contextDependent_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3576_; 
v_contextDependent_3565_ = lean_ctor_get_uint8(v_a_3561_, 1);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_a_3561_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3567_ = v_a_3561_;
v_isShared_3568_ = v_isSharedCheck_3576_;
goto v_resetjp_3566_;
}
else
{
lean_dec(v_a_3561_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3576_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
uint8_t v___x_3569_; lean_object* v___x_3571_; 
v___x_3569_ = 1;
if (v_isShared_3568_ == 0)
{
v___x_3571_ = v___x_3567_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_3575_, 1, v_contextDependent_3565_);
v___x_3571_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3573_; 
lean_ctor_set_uint8(v___x_3571_, 0, v___x_3569_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 0, v___x_3571_);
v___x_3573_ = v___x_3563_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
else
{
lean_object* v_e_x27_3577_; lean_object* v_proof_3578_; uint8_t v_contextDependent_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3590_; 
v_e_x27_3577_ = lean_ctor_get(v_a_3561_, 0);
v_proof_3578_ = lean_ctor_get(v_a_3561_, 1);
v_contextDependent_3579_ = lean_ctor_get_uint8(v_a_3561_, sizeof(void*)*2 + 1);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_a_3561_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3581_ = v_a_3561_;
v_isShared_3582_ = v_isSharedCheck_3590_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_proof_3578_);
lean_inc(v_e_x27_3577_);
lean_dec(v_a_3561_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3590_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
uint8_t v___x_3583_; lean_object* v___x_3585_; 
v___x_3583_ = 1;
if (v_isShared_3582_ == 0)
{
v___x_3585_ = v___x_3581_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_e_x27_3577_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_proof_3578_);
lean_ctor_set_uint8(v_reuseFailAlloc_3589_, sizeof(void*)*2 + 1, v_contextDependent_3579_);
v___x_3585_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3587_; 
lean_ctor_set_uint8(v___x_3585_, sizeof(void*)*2, v___x_3583_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 0, v___x_3585_);
v___x_3587_ = v___x_3563_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3585_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
}
else
{
return v___y_3560_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3548_ = stack[0].m_obj;
lean_object* v_a_3549_ = stack[1].m_obj;
lean_object* v_a_3550_ = stack[2].m_obj;
lean_object* v_a_3551_ = stack[3].m_obj;
lean_object* v_a_3552_ = stack[4].m_obj;
lean_object* v_a_3553_ = stack[5].m_obj;
lean_object* v_a_3554_ = stack[6].m_obj;
lean_object* v_a_3555_ = stack[7].m_obj;
lean_object* v_a_3556_ = stack[8].m_obj;
lean_object* v_a_3557_ = stack[9].m_obj;
lean_object* v_res_3673_;
v_res_3673_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(v_e_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
stack->m_obj
 = v_res_3673_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object* v_e_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(v_e_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
lean_dec(v_a_3683_);
lean_dec_ref(v_a_3682_);
lean_dec(v_a_3681_);
lean_dec_ref(v_a_3680_);
lean_dec(v_a_3679_);
lean_dec_ref(v_a_3678_);
lean_dec(v_a_3677_);
lean_dec_ref(v_a_3676_);
lean_dec(v_a_3675_);
return v_res_3685_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(lean_object* v_x_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
lean_object* v___x_3699_; 
lean_inc(v___y_3693_);
lean_inc_ref(v___y_3692_);
lean_inc(v___y_3691_);
lean_inc_ref(v___y_3690_);
lean_inc(v___y_3689_);
lean_inc(v___y_3688_);
lean_inc_ref(v___y_3687_);
v___x_3699_ = lean_apply_12(v_x_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, lean_box(0));
return v___x_3699_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3686_ = stack[0].m_obj;
lean_object* v___y_3687_ = stack[1].m_obj;
lean_object* v___y_3688_ = stack[2].m_obj;
lean_object* v___y_3689_ = stack[3].m_obj;
lean_object* v___y_3690_ = stack[4].m_obj;
lean_object* v___y_3691_ = stack[5].m_obj;
lean_object* v___y_3692_ = stack[6].m_obj;
lean_object* v___y_3693_ = stack[7].m_obj;
lean_object* v___y_3694_ = stack[8].m_obj;
lean_object* v___y_3695_ = stack[9].m_obj;
lean_object* v___y_3696_ = stack[10].m_obj;
lean_object* v___y_3697_ = stack[11].m_obj;
lean_object* v_res_3700_;
v_res_3700_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(v_x_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
stack->m_obj
 = v_res_3700_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed(lean_object* v_x_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(v_x_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
return v_res_3714_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_mvarId_3715_, lean_object* v_x_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v___f_3729_; lean_object* v___x_3730_; 
lean_inc(v___y_3723_);
lean_inc_ref(v___y_3722_);
lean_inc(v___y_3721_);
lean_inc_ref(v___y_3720_);
lean_inc(v___y_3719_);
lean_inc(v___y_3718_);
lean_inc_ref(v___y_3717_);
v___f_3729_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_3729_, 0, v_x_3716_);
lean_closure_set(v___f_3729_, 1, v___y_3717_);
lean_closure_set(v___f_3729_, 2, v___y_3718_);
lean_closure_set(v___f_3729_, 3, v___y_3719_);
lean_closure_set(v___f_3729_, 4, v___y_3720_);
lean_closure_set(v___f_3729_, 5, v___y_3721_);
lean_closure_set(v___f_3729_, 6, v___y_3722_);
lean_closure_set(v___f_3729_, 7, v___y_3723_);
v___x_3730_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3715_, v___f_3729_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
if (lean_obj_tag(v___x_3730_) == 0)
{
return v___x_3730_;
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3730_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3730_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3715_ = stack[0].m_obj;
lean_object* v_x_3716_ = stack[1].m_obj;
lean_object* v___y_3717_ = stack[2].m_obj;
lean_object* v___y_3718_ = stack[3].m_obj;
lean_object* v___y_3719_ = stack[4].m_obj;
lean_object* v___y_3720_ = stack[5].m_obj;
lean_object* v___y_3721_ = stack[6].m_obj;
lean_object* v___y_3722_ = stack[7].m_obj;
lean_object* v___y_3723_ = stack[8].m_obj;
lean_object* v___y_3724_ = stack[9].m_obj;
lean_object* v___y_3725_ = stack[10].m_obj;
lean_object* v___y_3726_ = stack[11].m_obj;
lean_object* v___y_3727_ = stack[12].m_obj;
lean_object* v_res_3739_;
v_res_3739_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3715_, v_x_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
stack->m_obj
 = v_res_3739_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_mvarId_3740_, lean_object* v_x_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3740_, v_x_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
return v_res_3754_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object* v_00_u03b1_3755_, lean_object* v_mvarId_3756_, lean_object* v_x_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3756_, v_x_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
return v___x_3770_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3756_ = stack[1].m_obj;
lean_object* v_x_3757_ = stack[2].m_obj;
lean_object* v___y_3758_ = stack[3].m_obj;
lean_object* v___y_3759_ = stack[4].m_obj;
lean_object* v___y_3760_ = stack[5].m_obj;
lean_object* v___y_3761_ = stack[6].m_obj;
lean_object* v___y_3762_ = stack[7].m_obj;
lean_object* v___y_3763_ = stack[8].m_obj;
lean_object* v___y_3764_ = stack[9].m_obj;
lean_object* v___y_3765_ = stack[10].m_obj;
lean_object* v___y_3766_ = stack[11].m_obj;
lean_object* v___y_3767_ = stack[12].m_obj;
lean_object* v___y_3768_ = stack[13].m_obj;
lean_object* v_res_3771_;
v_res_3771_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_box(0), v_mvarId_3756_, v_x_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
stack->m_obj
 = v_res_3771_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_00_u03b1_3772_, lean_object* v_mvarId_3773_, lean_object* v_x_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(v_00_u03b1_3772_, v_mvarId_3773_, v_x_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
return v_res_3787_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(lean_object* v_x_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
v___x_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3799_);
return v___x_3800_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3788_ = stack[0].m_obj;
lean_object* v___y_3789_ = stack[1].m_obj;
lean_object* v___y_3790_ = stack[2].m_obj;
lean_object* v___y_3791_ = stack[3].m_obj;
lean_object* v___y_3792_ = stack[4].m_obj;
lean_object* v___y_3793_ = stack[5].m_obj;
lean_object* v___y_3794_ = stack[6].m_obj;
lean_object* v___y_3795_ = stack[7].m_obj;
lean_object* v___y_3796_ = stack[8].m_obj;
lean_object* v___y_3797_ = stack[9].m_obj;
lean_object* v_res_3801_;
v_res_3801_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(v_x_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
stack->m_obj
 = v_res_3801_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0___boxed(lean_object* v_x_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(v_x_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v_x_3802_);
return v_res_3813_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(lean_object* v_snd_3814_, lean_object* v_a_3815_, lean_object* v___x_3816_, lean_object* v_____r_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3830_ = lean_array_push(v_snd_3814_, v_a_3815_);
v___x_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3816_);
lean_ctor_set(v___x_3831_, 1, v___x_3830_);
v___x_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
v___x_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
return v___x_3833_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_3814_ = stack[0].m_obj;
lean_object* v_a_3815_ = stack[1].m_obj;
lean_object* v___x_3816_ = stack[2].m_obj;
lean_object* v_____r_3817_ = stack[3].m_obj;
lean_object* v___y_3818_ = stack[4].m_obj;
lean_object* v___y_3819_ = stack[5].m_obj;
lean_object* v___y_3820_ = stack[6].m_obj;
lean_object* v___y_3821_ = stack[7].m_obj;
lean_object* v___y_3822_ = stack[8].m_obj;
lean_object* v___y_3823_ = stack[9].m_obj;
lean_object* v___y_3824_ = stack[10].m_obj;
lean_object* v___y_3825_ = stack[11].m_obj;
lean_object* v___y_3826_ = stack[12].m_obj;
lean_object* v___y_3827_ = stack[13].m_obj;
lean_object* v___y_3828_ = stack[14].m_obj;
lean_object* v_res_3834_;
v_res_3834_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3814_, v_a_3815_, v___x_3816_, v_____r_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
stack->m_obj
 = v_res_3834_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed(lean_object* v_snd_3835_, lean_object* v_a_3836_, lean_object* v___x_3837_, lean_object* v_____r_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3835_, v_a_3836_, v___x_3837_, v_____r_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
return v_res_3851_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_cls_3852_, lean_object* v_msg_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_ref_3859_; lean_object* v___x_3860_; lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3906_; 
v_ref_3859_ = lean_ctor_get(v___y_3856_, 2);
v___x_3860_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3906_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3906_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3865_; lean_object* v_traceState_3866_; lean_object* v_env_3867_; lean_object* v_nextMacroScope_3868_; lean_object* v_ngen_3869_; lean_object* v_auxDeclNGen_3870_; lean_object* v_cache_3871_; lean_object* v_recordedDeps_3872_; lean_object* v_messages_3873_; lean_object* v_infoState_3874_; lean_object* v_snapshotTasks_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3905_; 
v___x_3865_ = lean_st_ref_take(v___y_3857_);
v_traceState_3866_ = lean_ctor_get(v___x_3865_, 4);
v_env_3867_ = lean_ctor_get(v___x_3865_, 0);
v_nextMacroScope_3868_ = lean_ctor_get(v___x_3865_, 1);
v_ngen_3869_ = lean_ctor_get(v___x_3865_, 2);
v_auxDeclNGen_3870_ = lean_ctor_get(v___x_3865_, 3);
v_cache_3871_ = lean_ctor_get(v___x_3865_, 5);
v_recordedDeps_3872_ = lean_ctor_get(v___x_3865_, 6);
v_messages_3873_ = lean_ctor_get(v___x_3865_, 7);
v_infoState_3874_ = lean_ctor_get(v___x_3865_, 8);
v_snapshotTasks_3875_ = lean_ctor_get(v___x_3865_, 9);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3877_ = v___x_3865_;
v_isShared_3878_ = v_isSharedCheck_3905_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_snapshotTasks_3875_);
lean_inc(v_infoState_3874_);
lean_inc(v_messages_3873_);
lean_inc(v_recordedDeps_3872_);
lean_inc(v_cache_3871_);
lean_inc(v_traceState_3866_);
lean_inc(v_auxDeclNGen_3870_);
lean_inc(v_ngen_3869_);
lean_inc(v_nextMacroScope_3868_);
lean_inc(v_env_3867_);
lean_dec(v___x_3865_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3905_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
uint64_t v_tid_3879_; lean_object* v_traces_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3904_; 
v_tid_3879_ = lean_ctor_get_uint64(v_traceState_3866_, sizeof(void*)*1);
v_traces_3880_ = lean_ctor_get(v_traceState_3866_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v_traceState_3866_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3882_ = v_traceState_3866_;
v_isShared_3883_ = v_isSharedCheck_3904_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_traces_3880_);
lean_dec(v_traceState_3866_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3904_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; double v___x_3886_; uint8_t v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3884_ = lean_box(0);
v___x_3885_ = lean_box(0);
v___x_3886_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_3887_ = 0;
v___x_3888_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3889_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3889_, 0, v_cls_3852_);
lean_ctor_set(v___x_3889_, 1, v___x_3885_);
lean_ctor_set(v___x_3889_, 2, v___x_3888_);
lean_ctor_set_float(v___x_3889_, sizeof(void*)*3, v___x_3886_);
lean_ctor_set_float(v___x_3889_, sizeof(void*)*3 + 8, v___x_3886_);
lean_ctor_set_uint8(v___x_3889_, sizeof(void*)*3 + 16, v___x_3887_);
v___x_3890_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_3891_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3889_);
lean_ctor_set(v___x_3891_, 1, v_a_3861_);
lean_ctor_set(v___x_3891_, 2, v___x_3890_);
lean_inc(v_ref_3859_);
v___x_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3892_, 0, v_ref_3859_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
v___x_3893_ = l_Lean_PersistentArray_push___redArg(v_traces_3880_, v___x_3892_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 0, v___x_3893_);
v___x_3895_ = v___x_3882_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3893_);
lean_ctor_set_uint64(v_reuseFailAlloc_3903_, sizeof(void*)*1, v_tid_3879_);
v___x_3895_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3897_; 
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 4, v___x_3895_);
v___x_3897_ = v___x_3877_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_env_3867_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v_nextMacroScope_3868_);
lean_ctor_set(v_reuseFailAlloc_3902_, 2, v_ngen_3869_);
lean_ctor_set(v_reuseFailAlloc_3902_, 3, v_auxDeclNGen_3870_);
lean_ctor_set(v_reuseFailAlloc_3902_, 4, v___x_3895_);
lean_ctor_set(v_reuseFailAlloc_3902_, 5, v_cache_3871_);
lean_ctor_set(v_reuseFailAlloc_3902_, 6, v_recordedDeps_3872_);
lean_ctor_set(v_reuseFailAlloc_3902_, 7, v_messages_3873_);
lean_ctor_set(v_reuseFailAlloc_3902_, 8, v_infoState_3874_);
lean_ctor_set(v_reuseFailAlloc_3902_, 9, v_snapshotTasks_3875_);
v___x_3897_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3898_; lean_object* v___x_3900_; 
v___x_3898_ = lean_st_ref_put(v___y_3857_, v___x_3897_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3884_);
v___x_3900_ = v___x_3863_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3884_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3852_ = stack[0].m_obj;
lean_object* v_msg_3853_ = stack[1].m_obj;
lean_object* v___y_3854_ = stack[2].m_obj;
lean_object* v___y_3855_ = stack[3].m_obj;
lean_object* v___y_3856_ = stack[4].m_obj;
lean_object* v___y_3857_ = stack[5].m_obj;
lean_object* v_res_3907_;
v_res_3907_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_3852_, v_msg_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
stack->m_obj
 = v_res_3907_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_cls_3908_, lean_object* v_msg_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_3908_, v_msg_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
return v_res_3915_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(uint8_t v___x_3916_, lean_object* v___f_3917_, lean_object* v_____r_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v___x_3931_; lean_object* v_caches_3932_; lean_object* v_typeAnalysis_3933_; lean_object* v_target_3934_; lean_object* v_hypotheses_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3945_; 
v___x_3931_ = lean_st_ref_take(v___y_3920_);
v_caches_3932_ = lean_ctor_get(v___x_3931_, 0);
v_typeAnalysis_3933_ = lean_ctor_get(v___x_3931_, 1);
v_target_3934_ = lean_ctor_get(v___x_3931_, 2);
v_hypotheses_3935_ = lean_ctor_get(v___x_3931_, 3);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3937_ = v___x_3931_;
v_isShared_3938_ = v_isSharedCheck_3945_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_hypotheses_3935_);
lean_inc(v_target_3934_);
lean_inc(v_typeAnalysis_3933_);
lean_inc(v_caches_3932_);
lean_dec(v___x_3931_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3945_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3939_ = lean_box(0);
if (v_isShared_3938_ == 0)
{
v___x_3941_ = v___x_3937_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_caches_3932_);
lean_ctor_set(v_reuseFailAlloc_3944_, 1, v_typeAnalysis_3933_);
lean_ctor_set(v_reuseFailAlloc_3944_, 2, v_target_3934_);
lean_ctor_set(v_reuseFailAlloc_3944_, 3, v_hypotheses_3935_);
v___x_3941_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
lean_ctor_set_uint8(v___x_3941_, sizeof(void*)*4, v___x_3916_);
v___x_3942_ = lean_st_ref_put(v___y_3920_, v___x_3941_);
lean_inc(v___y_3929_);
lean_inc_ref(v___y_3928_);
lean_inc(v___y_3927_);
lean_inc_ref(v___y_3926_);
lean_inc(v___y_3925_);
lean_inc_ref(v___y_3924_);
lean_inc(v___y_3923_);
lean_inc_ref(v___y_3922_);
lean_inc(v___y_3921_);
lean_inc(v___y_3920_);
lean_inc_ref(v___y_3919_);
v___x_3943_ = lean_apply_13(v___f_3917_, v___x_3939_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, lean_box(0));
return v___x_3943_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3916_ = stack[0].m_num;
lean_object* v___f_3917_ = stack[1].m_obj;
lean_object* v_____r_3918_ = stack[2].m_obj;
lean_object* v___y_3919_ = stack[3].m_obj;
lean_object* v___y_3920_ = stack[4].m_obj;
lean_object* v___y_3921_ = stack[5].m_obj;
lean_object* v___y_3922_ = stack[6].m_obj;
lean_object* v___y_3923_ = stack[7].m_obj;
lean_object* v___y_3924_ = stack[8].m_obj;
lean_object* v___y_3925_ = stack[9].m_obj;
lean_object* v___y_3926_ = stack[10].m_obj;
lean_object* v___y_3927_ = stack[11].m_obj;
lean_object* v___y_3928_ = stack[12].m_obj;
lean_object* v___y_3929_ = stack[13].m_obj;
lean_object* v_res_3946_;
v_res_3946_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3916_, v___f_3917_, v_____r_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
stack->m_obj
 = v_res_3946_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2___boxed(lean_object* v___x_3947_, lean_object* v___f_3948_, lean_object* v_____r_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
uint8_t v___x_10287__boxed_3962_; lean_object* v_res_3963_; 
v___x_10287__boxed_3962_ = lean_unbox(v___x_3947_);
v_res_3963_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_10287__boxed_3962_, v___f_3948_, v_____r_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
return v_res_3963_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3965_; lean_object* v___f_3966_; lean_object* v_methods_3967_; 
v___x_3965_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 11, 0);
v___f_3966_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0));
v_methods_3967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_methods_3967_, 0, v___f_3966_);
lean_ctor_set(v_methods_3967_, 1, v___x_3965_);
return v_methods_3967_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2));
v___x_3970_ = l_Lean_stringToMessageData(v___x_3969_);
return v___x_3970_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_upperBound_3971_, lean_object* v___x_3972_, lean_object* v_config_3973_, lean_object* v_a_3974_, lean_object* v_b_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v___y_3989_; uint8_t v___x_4011_; 
v___x_4011_ = lean_nat_dec_lt(v_a_3974_, v_upperBound_3971_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; 
lean_dec(v_a_3974_);
lean_dec_ref(v_config_3973_);
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v_b_3975_);
return v___x_4012_;
}
else
{
lean_object* v_snd_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4089_; 
v_snd_4013_ = lean_ctor_get(v_b_3975_, 1);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_b_3975_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; 
v_unused_4090_ = lean_ctor_get(v_b_3975_, 0);
lean_dec(v_unused_4090_);
v___x_4015_ = v_b_3975_;
v_isShared_4016_ = v_isSharedCheck_4089_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_snd_4013_);
lean_dec(v_b_3975_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4089_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
uint8_t v___x_4017_; lean_object* v_methods_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4017_ = 1;
v_methods_4018_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1);
v___x_4019_ = lean_box(0);
v___x_4020_ = lean_array_fget_borrowed(v___x_3972_, v_a_3974_);
lean_inc(v___x_4020_);
lean_inc_ref(v_config_3973_);
v___x_4021_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v___x_4017_, v_methods_4018_, v_config_3973_, v___x_4020_, v___y_3977_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v_type_4023_; lean_object* v_value_4024_; uint8_t v___x_4025_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v___x_4021_, 1);
v_type_4023_ = lean_ctor_get(v_a_4022_, 1);
v_value_4024_ = lean_ctor_get(v_a_4022_, 2);
lean_inc_ref(v_type_4023_);
v___x_4025_ = l_Lean_Expr_isFalse(v_type_4023_);
if (v___x_4025_ == 0)
{
lean_object* v_type_4026_; lean_object* v___f_4027_; uint8_t v___x_4056_; 
lean_del_object(v___x_4015_);
v_type_4026_ = lean_ctor_get(v___x_4020_, 1);
lean_inc(v_a_4022_);
lean_inc(v_snd_4013_);
v___f_4027_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_4027_, 0, v_snd_4013_);
lean_closure_set(v___f_4027_, 1, v_a_4022_);
lean_closure_set(v___f_4027_, 2, v___x_4019_);
v___x_4056_ = lean_expr_eqv(v_type_4026_, v_type_4023_);
if (v___x_4056_ == 0)
{
lean_inc_ref(v_type_4023_);
lean_dec(v_a_4022_);
lean_dec(v_snd_4013_);
goto v___jp_4031_;
}
else
{
if (v___x_4025_ == 0)
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
lean_dec_ref(v___f_4027_);
v___x_4057_ = lean_box(0);
v___x_4058_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_4013_, v_a_4022_, v___x_4019_, v___x_4057_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
v___y_3989_ = v___x_4058_;
goto v___jp_3988_;
}
else
{
lean_inc_ref(v_type_4023_);
lean_dec(v_a_4022_);
lean_dec(v_snd_4013_);
goto v___jp_4031_;
}
}
v___jp_4028_:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = lean_box(0);
v___x_4030_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_4011_, v___f_4027_, v___x_4029_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
v___y_3989_ = v___x_4030_;
goto v___jp_3988_;
}
v___jp_4031_:
{
lean_object* v_toCold_4032_; lean_object* v_options_4033_; uint8_t v_hasTrace_4034_; 
v_toCold_4032_ = lean_ctor_get(v___y_3985_, 0);
v_options_4033_ = lean_ctor_get(v_toCold_4032_, 2);
v_hasTrace_4034_ = lean_ctor_get_uint8(v_options_4033_, sizeof(void*)*1);
if (v_hasTrace_4034_ == 0)
{
lean_dec_ref(v_type_4023_);
goto v___jp_4028_;
}
else
{
lean_object* v_inheritedTraceOptions_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; uint8_t v___x_4038_; 
v_inheritedTraceOptions_4035_ = lean_ctor_get(v_toCold_4032_, 11);
v___x_4036_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_4037_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_4038_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4035_, v_options_4033_, v___x_4037_);
if (v___x_4038_ == 0)
{
lean_dec_ref(v_type_4023_);
goto v___jp_4028_;
}
else
{
lean_object* v_type_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v_type_4039_ = lean_ctor_get(v___x_4020_, 1);
lean_inc_ref(v_type_4039_);
v___x_4040_ = l_Lean_MessageData_ofExpr(v_type_4039_);
v___x_4041_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3);
v___x_4042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4040_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = l_Lean_MessageData_ofExpr(v_type_4023_);
v___x_4044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4042_);
lean_ctor_set(v___x_4044_, 1, v___x_4043_);
v___x_4045_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v___x_4036_, v___x_4044_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_a_4046_; lean_object* v___x_4047_; 
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
lean_inc(v_a_4046_);
lean_dec_ref_known(v___x_4045_, 1);
v___x_4047_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_4011_, v___f_4027_, v_a_4046_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
v___y_3989_ = v___x_4047_;
goto v___jp_3988_;
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec_ref(v___f_4027_);
lean_dec(v_a_3974_);
lean_dec_ref(v_config_3973_);
v_a_4048_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4045_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4045_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4059_; 
lean_inc_ref(v_value_4024_);
lean_dec(v_a_4022_);
lean_dec(v_a_3974_);
lean_dec_ref(v_config_3973_);
v___x_4059_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_4024_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4071_; 
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4071_ == 0)
{
lean_object* v_unused_4072_; 
v_unused_4072_ = lean_ctor_get(v___x_4059_, 0);
lean_dec(v_unused_4072_);
v___x_4061_ = v___x_4059_;
v_isShared_4062_ = v_isSharedCheck_4071_;
goto v_resetjp_4060_;
}
else
{
lean_dec(v___x_4059_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4071_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4066_; 
v___x_4063_ = lean_box(v___x_4011_);
v___x_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4063_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 0, v___x_4064_);
v___x_4066_ = v___x_4015_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4064_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_snd_4013_);
v___x_4066_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
lean_object* v___x_4068_; 
if (v_isShared_4062_ == 0)
{
lean_ctor_set(v___x_4061_, 0, v___x_4066_);
v___x_4068_ = v___x_4061_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4066_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_del_object(v___x_4015_);
lean_dec(v_snd_4013_);
v_a_4073_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4059_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4059_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_del_object(v___x_4015_);
lean_dec(v_snd_4013_);
lean_dec(v_a_3974_);
lean_dec_ref(v_config_3973_);
v_a_4081_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4021_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4021_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
}
v___jp_3988_:
{
if (lean_obj_tag(v___y_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4002_; 
v_a_3990_ = lean_ctor_get(v___y_3989_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___y_3989_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3992_ = v___y_3989_;
v_isShared_3993_ = v_isSharedCheck_4002_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___y_3989_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4002_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
if (lean_obj_tag(v_a_3990_) == 0)
{
lean_object* v_a_3994_; lean_object* v___x_3996_; 
lean_dec(v_a_3974_);
lean_dec_ref(v_config_3973_);
v_a_3994_ = lean_ctor_get(v_a_3990_, 0);
lean_inc(v_a_3994_);
lean_dec_ref_known(v_a_3990_, 1);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v_a_3994_);
v___x_3996_ = v___x_3992_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3994_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
lean_del_object(v___x_3992_);
v_a_3998_ = lean_ctor_get(v_a_3990_, 0);
lean_inc(v_a_3998_);
lean_dec_ref_known(v_a_3990_, 1);
v___x_3999_ = lean_unsigned_to_nat(1u);
v___x_4000_ = lean_nat_add(v_a_3974_, v___x_3999_);
lean_dec(v_a_3974_);
v_a_3974_ = v___x_4000_;
v_b_3975_ = v_a_3998_;
goto _start;
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec(v_a_3974_);
lean_dec_ref(v_config_3973_);
v_a_4003_ = lean_ctor_get(v___y_3989_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___y_3989_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___y_3989_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___y_3989_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3971_ = stack[0].m_obj;
lean_object* v___x_3972_ = stack[1].m_obj;
lean_object* v_config_3973_ = stack[2].m_obj;
lean_object* v_a_3974_ = stack[3].m_obj;
lean_object* v_b_3975_ = stack[4].m_obj;
lean_object* v___y_3976_ = stack[5].m_obj;
lean_object* v___y_3977_ = stack[6].m_obj;
lean_object* v___y_3978_ = stack[7].m_obj;
lean_object* v___y_3979_ = stack[8].m_obj;
lean_object* v___y_3980_ = stack[9].m_obj;
lean_object* v___y_3981_ = stack[10].m_obj;
lean_object* v___y_3982_ = stack[11].m_obj;
lean_object* v___y_3983_ = stack[12].m_obj;
lean_object* v___y_3984_ = stack[13].m_obj;
lean_object* v___y_3985_ = stack[14].m_obj;
lean_object* v___y_3986_ = stack[15].m_obj;
lean_object* v_res_4091_;
v_res_4091_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_3971_, v___x_3972_, v_config_3973_, v_a_3974_, v_b_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
stack->m_obj
 = v_res_4091_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_4092_ = _args[0];
lean_object* v___x_4093_ = _args[1];
lean_object* v_config_4094_ = _args[2];
lean_object* v_a_4095_ = _args[3];
lean_object* v_b_4096_ = _args[4];
lean_object* v___y_4097_ = _args[5];
lean_object* v___y_4098_ = _args[6];
lean_object* v___y_4099_ = _args[7];
lean_object* v___y_4100_ = _args[8];
lean_object* v___y_4101_ = _args[9];
lean_object* v___y_4102_ = _args[10];
lean_object* v___y_4103_ = _args[11];
lean_object* v___y_4104_ = _args[12];
lean_object* v___y_4105_ = _args[13];
lean_object* v___y_4106_ = _args[14];
lean_object* v___y_4107_ = _args[15];
lean_object* v___y_4108_ = _args[16];
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4092_, v___x_4093_, v_config_4094_, v_a_4095_, v_b_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec_ref(v___x_4093_);
lean_dec(v_upperBound_4092_);
return v_res_4109_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object* v_config_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v___x_4123_; lean_object* v_hypotheses_4124_; lean_object* v___x_4125_; lean_object* v_newHyps_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4123_ = lean_st_ref_get(v___y_4112_);
v_hypotheses_4124_ = lean_ctor_get(v___x_4123_, 3);
lean_inc_ref(v_hypotheses_4124_);
lean_dec(v___x_4123_);
v___x_4125_ = lean_array_get_size(v_hypotheses_4124_);
v_newHyps_4126_ = lean_mk_empty_array_with_capacity(v___x_4125_);
v___x_4127_ = lean_unsigned_to_nat(0u);
v___x_4128_ = lean_box(0);
v___x_4129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4128_);
lean_ctor_set(v___x_4129_, 1, v_newHyps_4126_);
v___x_4130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v___x_4125_, v_hypotheses_4124_, v_config_4110_, v___x_4127_, v___x_4129_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
lean_dec_ref(v_hypotheses_4124_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4160_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4133_ = v___x_4130_;
v_isShared_4134_ = v_isSharedCheck_4160_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4130_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4160_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v_fst_4135_; 
v_fst_4135_ = lean_ctor_get(v_a_4131_, 0);
if (lean_obj_tag(v_fst_4135_) == 0)
{
lean_object* v_snd_4136_; lean_object* v___x_4137_; lean_object* v_caches_4138_; lean_object* v_typeAnalysis_4139_; lean_object* v_target_4140_; uint8_t v_didChange_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4154_; 
v_snd_4136_ = lean_ctor_get(v_a_4131_, 1);
lean_inc(v_snd_4136_);
lean_dec(v_a_4131_);
v___x_4137_ = lean_st_ref_take(v___y_4112_);
v_caches_4138_ = lean_ctor_get(v___x_4137_, 0);
v_typeAnalysis_4139_ = lean_ctor_get(v___x_4137_, 1);
v_target_4140_ = lean_ctor_get(v___x_4137_, 2);
v_didChange_4141_ = lean_ctor_get_uint8(v___x_4137_, sizeof(void*)*4);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4154_ == 0)
{
lean_object* v_unused_4155_; 
v_unused_4155_ = lean_ctor_get(v___x_4137_, 3);
lean_dec(v_unused_4155_);
v___x_4143_ = v___x_4137_;
v_isShared_4144_ = v_isSharedCheck_4154_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_target_4140_);
lean_inc(v_typeAnalysis_4139_);
lean_inc(v_caches_4138_);
lean_dec(v___x_4137_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4154_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 3, v_snd_4136_);
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_caches_4138_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_typeAnalysis_4139_);
lean_ctor_set(v_reuseFailAlloc_4153_, 2, v_target_4140_);
lean_ctor_set(v_reuseFailAlloc_4153_, 3, v_snd_4136_);
lean_ctor_set_uint8(v_reuseFailAlloc_4153_, sizeof(void*)*4, v_didChange_4141_);
v___x_4146_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
lean_object* v___x_4147_; uint8_t v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4151_; 
v___x_4147_ = lean_st_ref_put(v___y_4112_, v___x_4146_);
v___x_4148_ = 0;
v___x_4149_ = lean_box(v___x_4148_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v___x_4149_);
v___x_4151_ = v___x_4133_;
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
lean_inc_ref(v_fst_4135_);
lean_dec(v_a_4131_);
v_val_4156_ = lean_ctor_get(v_fst_4135_, 0);
lean_inc(v_val_4156_);
lean_dec_ref_known(v_fst_4135_, 1);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v_val_4156_);
v___x_4158_ = v___x_4133_;
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
v_a_4161_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4130_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4130_);
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
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_4110_ = stack[0].m_obj;
lean_object* v___y_4111_ = stack[1].m_obj;
lean_object* v___y_4112_ = stack[2].m_obj;
lean_object* v___y_4113_ = stack[3].m_obj;
lean_object* v___y_4114_ = stack[4].m_obj;
lean_object* v___y_4115_ = stack[5].m_obj;
lean_object* v___y_4116_ = stack[6].m_obj;
lean_object* v___y_4117_ = stack[7].m_obj;
lean_object* v___y_4118_ = stack[8].m_obj;
lean_object* v___y_4119_ = stack[9].m_obj;
lean_object* v___y_4120_ = stack[10].m_obj;
lean_object* v___y_4121_ = stack[11].m_obj;
lean_object* v_res_4169_;
v_res_4169_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(v_config_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
stack->m_obj
 = v_res_4169_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v_config_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(v_config_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
return v_res_4183_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_config_4196_; lean_object* v_maxSteps_4197_; lean_object* v___x_4198_; lean_object* v_config_4199_; lean_object* v___f_4200_; lean_object* v___x_4201_; lean_object* v_target_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v_config_4196_ = lean_ctor_get(v___y_4184_, 0);
v_maxSteps_4197_ = lean_ctor_get(v_config_4196_, 1);
v___x_4198_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_4197_);
v_config_4199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_4199_, 0, v_maxSteps_4197_);
lean_ctor_set(v_config_4199_, 1, v___x_4198_);
v___f_4200_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_4200_, 0, v_config_4199_);
v___x_4201_ = lean_st_ref_get(v___y_4185_);
v_target_4202_ = lean_ctor_get(v___x_4201_, 2);
lean_inc_ref(v_target_4202_);
lean_dec(v___x_4201_);
v___x_4203_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_4202_);
lean_dec_ref(v_target_4202_);
v___x_4204_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v___x_4203_, v___f_4200_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
return v___x_4204_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4184_ = stack[0].m_obj;
lean_object* v___y_4185_ = stack[1].m_obj;
lean_object* v___y_4186_ = stack[2].m_obj;
lean_object* v___y_4187_ = stack[3].m_obj;
lean_object* v___y_4188_ = stack[4].m_obj;
lean_object* v___y_4189_ = stack[5].m_obj;
lean_object* v___y_4190_ = stack[6].m_obj;
lean_object* v___y_4191_ = stack[7].m_obj;
lean_object* v___y_4192_ = stack[8].m_obj;
lean_object* v___y_4193_ = stack[9].m_obj;
lean_object* v___y_4194_ = stack[10].m_obj;
lean_object* v_res_4205_;
v_res_4205_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
stack->m_obj
 = v_res_4205_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
return v_res_4218_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object* v_cls_4227_, lean_object* v_msg_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_4227_, v_msg_4228_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
return v___x_4241_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4227_ = stack[0].m_obj;
lean_object* v_msg_4228_ = stack[1].m_obj;
lean_object* v___y_4229_ = stack[2].m_obj;
lean_object* v___y_4230_ = stack[3].m_obj;
lean_object* v___y_4231_ = stack[4].m_obj;
lean_object* v___y_4232_ = stack[5].m_obj;
lean_object* v___y_4233_ = stack[6].m_obj;
lean_object* v___y_4234_ = stack[7].m_obj;
lean_object* v___y_4235_ = stack[8].m_obj;
lean_object* v___y_4236_ = stack[9].m_obj;
lean_object* v___y_4237_ = stack[10].m_obj;
lean_object* v___y_4238_ = stack[11].m_obj;
lean_object* v___y_4239_ = stack[12].m_obj;
lean_object* v_res_4242_;
v_res_4242_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(v_cls_4227_, v_msg_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
stack->m_obj
 = v_res_4242_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_cls_4243_, lean_object* v_msg_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(v_cls_4243_, v_msg_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
return v_res_4257_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object* v_upperBound_4258_, lean_object* v___x_4259_, lean_object* v_config_4260_, lean_object* v_inst_4261_, lean_object* v_R_4262_, lean_object* v_a_4263_, lean_object* v_b_4264_, lean_object* v_c_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v___x_4278_; 
v___x_4278_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4258_, v___x_4259_, v_config_4260_, v_a_4263_, v_b_4264_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
return v___x_4278_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4258_ = stack[0].m_obj;
lean_object* v___x_4259_ = stack[1].m_obj;
lean_object* v_config_4260_ = stack[2].m_obj;
lean_object* v_a_4263_ = stack[5].m_obj;
lean_object* v_b_4264_ = stack[6].m_obj;
lean_object* v___y_4266_ = stack[8].m_obj;
lean_object* v___y_4267_ = stack[9].m_obj;
lean_object* v___y_4268_ = stack[10].m_obj;
lean_object* v___y_4269_ = stack[11].m_obj;
lean_object* v___y_4270_ = stack[12].m_obj;
lean_object* v___y_4271_ = stack[13].m_obj;
lean_object* v___y_4272_ = stack[14].m_obj;
lean_object* v___y_4273_ = stack[15].m_obj;
lean_object* v___y_4274_ = stack[16].m_obj;
lean_object* v___y_4275_ = stack[17].m_obj;
lean_object* v___y_4276_ = stack[18].m_obj;
lean_object* v_res_4279_;
v_res_4279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(v_upperBound_4258_, v___x_4259_, v_config_4260_, lean_box(0), lean_box(0), v_a_4263_, v_b_4264_, lean_box(0), v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
stack->m_obj
 = v_res_4279_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_4280_ = _args[0];
lean_object* v___x_4281_ = _args[1];
lean_object* v_config_4282_ = _args[2];
lean_object* v_inst_4283_ = _args[3];
lean_object* v_R_4284_ = _args[4];
lean_object* v_a_4285_ = _args[5];
lean_object* v_b_4286_ = _args[6];
lean_object* v_c_4287_ = _args[7];
lean_object* v___y_4288_ = _args[8];
lean_object* v___y_4289_ = _args[9];
lean_object* v___y_4290_ = _args[10];
lean_object* v___y_4291_ = _args[11];
lean_object* v___y_4292_ = _args[12];
lean_object* v___y_4293_ = _args[13];
lean_object* v___y_4294_ = _args[14];
lean_object* v___y_4295_ = _args[15];
lean_object* v___y_4296_ = _args[16];
lean_object* v___y_4297_ = _args[17];
lean_object* v___y_4298_ = _args[18];
lean_object* v___y_4299_ = _args[19];
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(v_upperBound_4280_, v___x_4281_, v_config_4282_, v_inst_4283_, v_R_4284_, v_a_4285_, v_b_4286_, v_c_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec_ref(v___x_4281_);
lean_dec(v_upperBound_4280_);
return v_res_4300_;
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
