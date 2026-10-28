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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Operations mismatch:\n      the left-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\n        "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "\n      but the right-hand-side has operation "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Canonicalizing with respect to operation: '"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to recognize operation: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7___boxed(lean_object**);
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
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Canonicalizing: "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_ac_nf "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " found `BEq.beq`."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " found `Eq`."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__12;
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
lean_dec_ref(v___x_92_);
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
lean_dec_ref(v___x_95_);
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
lean_dec_ref(v___x_98_);
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
lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_104_ = l_Lean_Expr_appFnCleanup___redArg(v___x_101_);
v___x_105_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2));
v___x_106_ = l_Lean_Expr_isConstOf(v___x_104_, v___x_105_);
lean_dec_ref(v___x_104_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
lean_dec_ref(v___x_101_);
v___x_107_ = lean_box(0);
return v___x_107_;
}
else
{
lean_object* v_arg_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v_arg_108_ = lean_ctor_get(v___x_101_, 1);
lean_inc_ref(v_arg_108_);
lean_dec_ref(v___x_101_);
v___x_109_ = l_Lean_Expr_cleanupAnnotations(v_arg_108_);
lean_dec_ref(v_arg_108_);
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
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_109_);
v___x_113_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType___closed__1));
v___x_114_ = l_Lean_Expr_isConstOf(v___x_112_, v___x_113_);
lean_dec_ref(v___x_112_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
lean_dec_ref(v___x_109_);
v___x_115_ = lean_box(0);
return v___x_115_;
}
else
{
lean_object* v_arg_116_; lean_object* v___x_117_; 
v_arg_116_ = lean_ctor_get(v___x_109_, 1);
lean_inc_ref(v_arg_116_);
lean_dec_ref(v___x_109_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v_arg_116_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___boxed(lean_object* v_e_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(v_e_118_);
lean_dec_ref(v_e_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(lean_object* v_x_120_){
_start:
{
if (lean_obj_tag(v_x_120_) == 5)
{
lean_object* v_fn_121_; 
v_fn_121_ = lean_ctor_get(v_x_120_, 0);
if (lean_obj_tag(v_fn_121_) == 5)
{
lean_object* v_fn_122_; lean_object* v___x_123_; 
v_fn_122_ = lean_ctor_get(v_fn_121_, 0);
v___x_123_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(v_fn_122_);
return v___x_123_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = lean_box(0);
return v___x_124_;
}
}
else
{
lean_object* v___x_125_; 
v___x_125_ = lean_box(0);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f___boxed(lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_x_126_);
lean_dec_ref(v_x_126_);
return v_res_127_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = l_Lean_Level_ofNat(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_box(0);
v___x_131_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0);
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__1);
v___x_134_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0);
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__2);
v___x_137_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__0);
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__3);
v___x_140_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f___closed__2));
v___x_141_ = l_Lean_mkConst(v___x_140_, v___x_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(lean_object* v_x_142_){
_start:
{
lean_object* v_bv_143_; lean_object* v_inst_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
lean_inc_ref(v_x_142_);
v_bv_143_ = l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkType(v_x_142_);
v_inst_144_ = l_Lean_Meta_Tactic_BVDecide_Normalize_BitVec_mkInstHMul(v_x_142_);
v___x_145_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr___closed__4);
lean_inc_ref_n(v_bv_143_, 2);
v___x_146_ = l_Lean_mkApp4(v___x_145_, v_bv_143_, v_bv_143_, v_bv_143_, v_inst_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(lean_object* v_x_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = l_Lean_Meta_Tactic_BVDecide_Normalize_mkBitVecLit(v_x_147_, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(lean_object* v_op_x27_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofExpr_x3f(v_op_x27_150_);
if (lean_obj_tag(v___x_151_) == 1)
{
uint8_t v___x_152_; 
lean_dec_ref_known(v___x_151_, 1);
v___x_152_ = 1;
return v___x_152_;
}
else
{
uint8_t v___x_153_; 
lean_dec(v___x_151_);
v___x_153_ = 0;
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg___boxed(lean_object* v_op_x27_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_op_x27_154_);
lean_dec_ref(v_op_x27_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind(lean_object* v_op_157_, lean_object* v_op_x27_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_op_x27_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___boxed(lean_object* v_op_160_, lean_object* v_op_x27_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind(v_op_160_, v_op_x27_161_);
lean_dec_ref(v_op_x27_161_);
lean_dec_ref(v_op_160_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Op_instToMessageData___lam__0(lean_object* v_op_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_164_);
v___x_166_ = l_Lean_MessageData_ofExpr(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(lean_object* v_x_169_, lean_object* v_s_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_178_; 
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc(v_a_174_);
lean_inc_ref(v_a_173_);
lean_inc(v_a_172_);
lean_inc_ref(v_a_171_);
v___x_178_ = lean_apply_8(v_x_169_, v_s_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, lean_box(0));
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_187_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_187_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v_fst_183_; lean_object* v___x_185_; 
v_fst_183_ = lean_ctor_get(v_a_179_, 0);
lean_inc(v_fst_183_);
lean_dec(v_a_179_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v_fst_183_);
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_fst_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
v_a_188_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_178_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_178_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(lean_object* v_00_u03b1_206_, lean_object* v_x_207_, lean_object* v_s_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v_x_207_, v_s_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___boxed(lean_object* v_00_u03b1_217_, lean_object* v_x_218_, lean_object* v_s_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27(v_00_u03b1_217_, v_x_218_, v_s_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(lean_object* v_a_228_, lean_object* v_b_229_, lean_object* v_x_230_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
lean_dec(v_b_229_);
lean_dec_ref(v_a_228_);
return v_x_230_;
}
else
{
lean_object* v_key_231_; lean_object* v_value_232_; lean_object* v_tail_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_245_; 
v_key_231_ = lean_ctor_get(v_x_230_, 0);
v_value_232_ = lean_ctor_get(v_x_230_, 1);
v_tail_233_ = lean_ctor_get(v_x_230_, 2);
v_isSharedCheck_245_ = !lean_is_exclusive(v_x_230_);
if (v_isSharedCheck_245_ == 0)
{
v___x_235_ = v_x_230_;
v_isShared_236_ = v_isSharedCheck_245_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_tail_233_);
lean_inc(v_value_232_);
lean_inc(v_key_231_);
lean_dec(v_x_230_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_245_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
uint8_t v___x_237_; 
v___x_237_ = lean_expr_eqv(v_key_231_, v_a_228_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_238_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_228_, v_b_229_, v_tail_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 2, v___x_238_);
v___x_240_ = v___x_235_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_key_231_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_value_232_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
lean_object* v___x_243_; 
lean_dec(v_value_232_);
lean_dec(v_key_231_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_b_229_);
lean_ctor_set(v___x_235_, 0, v_a_228_);
v___x_243_ = v___x_235_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_228_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_b_229_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v_tail_233_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(lean_object* v_a_246_, lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
else
{
lean_object* v_key_249_; lean_object* v_tail_250_; uint8_t v___x_251_; 
v_key_249_ = lean_ctor_get(v_x_247_, 0);
v_tail_250_ = lean_ctor_get(v_x_247_, 2);
v___x_251_ = lean_expr_eqv(v_key_249_, v_a_246_);
if (v___x_251_ == 0)
{
v_x_247_ = v_tail_250_;
goto _start;
}
else
{
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg___boxed(lean_object* v_a_253_, lean_object* v_x_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_253_, v_x_254_);
lean_dec(v_x_254_);
lean_dec_ref(v_a_253_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
return v_x_257_;
}
else
{
lean_object* v_key_259_; lean_object* v_value_260_; lean_object* v_tail_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_284_; 
v_key_259_ = lean_ctor_get(v_x_258_, 0);
v_value_260_ = lean_ctor_get(v_x_258_, 1);
v_tail_261_ = lean_ctor_get(v_x_258_, 2);
v_isSharedCheck_284_ = !lean_is_exclusive(v_x_258_);
if (v_isSharedCheck_284_ == 0)
{
v___x_263_ = v_x_258_;
v_isShared_264_ = v_isSharedCheck_284_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_tail_261_);
lean_inc(v_value_260_);
lean_inc(v_key_259_);
lean_dec(v_x_258_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_284_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; uint64_t v___x_266_; uint64_t v___x_267_; uint64_t v___x_268_; uint64_t v_fold_269_; uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v___x_272_; size_t v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_265_ = lean_array_get_size(v_x_257_);
v___x_266_ = l_Lean_Expr_hash(v_key_259_);
v___x_267_ = 32ULL;
v___x_268_ = lean_uint64_shift_right(v___x_266_, v___x_267_);
v_fold_269_ = lean_uint64_xor(v___x_266_, v___x_268_);
v___x_270_ = 16ULL;
v___x_271_ = lean_uint64_shift_right(v_fold_269_, v___x_270_);
v___x_272_ = lean_uint64_xor(v_fold_269_, v___x_271_);
v___x_273_ = lean_uint64_to_usize(v___x_272_);
v___x_274_ = lean_usize_of_nat(v___x_265_);
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_sub(v___x_274_, v___x_275_);
v___x_277_ = lean_usize_land(v___x_273_, v___x_276_);
v___x_278_ = lean_array_uget_borrowed(v_x_257_, v___x_277_);
lean_inc(v___x_278_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 2, v___x_278_);
v___x_280_ = v___x_263_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_key_259_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_value_260_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v___x_278_);
v___x_280_ = v_reuseFailAlloc_283_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_281_; 
v___x_281_ = lean_array_uset(v_x_257_, v___x_277_, v___x_280_);
v_x_257_ = v___x_281_;
v_x_258_ = v_tail_261_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(lean_object* v_i_285_, lean_object* v_source_286_, lean_object* v_target_287_){
_start:
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_array_get_size(v_source_286_);
v___x_289_ = lean_nat_dec_lt(v_i_285_, v___x_288_);
if (v___x_289_ == 0)
{
lean_dec_ref(v_source_286_);
lean_dec(v_i_285_);
return v_target_287_;
}
else
{
lean_object* v_es_290_; lean_object* v___x_291_; lean_object* v_source_292_; lean_object* v_target_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_es_290_ = lean_array_fget(v_source_286_, v_i_285_);
v___x_291_ = lean_box(0);
v_source_292_ = lean_array_fset(v_source_286_, v_i_285_, v___x_291_);
v_target_293_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_287_, v_es_290_);
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_nat_add(v_i_285_, v___x_294_);
lean_dec(v_i_285_);
v_i_285_ = v___x_295_;
v_source_286_ = v_source_292_;
v_target_287_ = v_target_293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(lean_object* v_data_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_nbuckets_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_298_ = lean_array_get_size(v_data_297_);
v___x_299_ = lean_unsigned_to_nat(2u);
v_nbuckets_300_ = lean_nat_mul(v___x_298_, v___x_299_);
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = lean_box(0);
v___x_303_ = lean_mk_array(v_nbuckets_300_, v___x_302_);
v___x_304_ = lean_array_propagate_mark(v_data_297_, v___x_303_);
v___x_305_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v___x_301_, v_data_297_, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(lean_object* v_m_306_, lean_object* v_a_307_, lean_object* v_b_308_){
_start:
{
lean_object* v_size_309_; lean_object* v_buckets_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_353_; 
v_size_309_ = lean_ctor_get(v_m_306_, 0);
v_buckets_310_ = lean_ctor_get(v_m_306_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v_m_306_);
if (v_isSharedCheck_353_ == 0)
{
v___x_312_ = v_m_306_;
v_isShared_313_ = v_isSharedCheck_353_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_buckets_310_);
lean_inc(v_size_309_);
lean_dec(v_m_306_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_353_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v_fold_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v_bkt_327_; uint8_t v___x_328_; 
v___x_314_ = lean_array_get_size(v_buckets_310_);
v___x_315_ = l_Lean_Expr_hash(v_a_307_);
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
v_bkt_327_ = lean_array_uget_borrowed(v_buckets_310_, v___x_326_);
v___x_328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_307_, v_bkt_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v_size_x27_330_; lean_object* v___x_331_; lean_object* v_buckets_x27_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v_size_x27_330_ = lean_nat_add(v_size_309_, v___x_329_);
lean_dec(v_size_309_);
lean_inc(v_bkt_327_);
v___x_331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_331_, 0, v_a_307_);
lean_ctor_set(v___x_331_, 1, v_b_308_);
lean_ctor_set(v___x_331_, 2, v_bkt_327_);
v_buckets_x27_332_ = lean_array_uset(v_buckets_310_, v___x_326_, v___x_331_);
v___x_333_ = lean_unsigned_to_nat(4u);
v___x_334_ = lean_nat_mul(v_size_x27_330_, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(3u);
v___x_336_ = lean_nat_div(v___x_334_, v___x_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_array_get_size(v_buckets_x27_332_);
v___x_338_ = lean_nat_dec_le(v___x_336_, v___x_337_);
lean_dec(v___x_336_);
if (v___x_338_ == 0)
{
lean_object* v_val_339_; lean_object* v___x_341_; 
v_val_339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_buckets_x27_332_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v_val_339_);
lean_ctor_set(v___x_312_, 0, v_size_x27_330_);
v___x_341_ = v___x_312_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_size_x27_330_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_val_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
lean_object* v___x_344_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v_buckets_x27_332_);
lean_ctor_set(v___x_312_, 0, v_size_x27_330_);
v___x_344_ = v___x_312_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_size_x27_330_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_buckets_x27_332_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
lean_object* v___x_346_; lean_object* v_buckets_x27_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
lean_inc(v_bkt_327_);
v___x_346_ = lean_box(0);
v_buckets_x27_347_ = lean_array_uset(v_buckets_310_, v___x_326_, v___x_346_);
v___x_348_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_307_, v_b_308_, v_bkt_327_);
v___x_349_ = lean_array_uset(v_buckets_x27_347_, v___x_326_, v___x_348_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v___x_349_);
v___x_351_ = v___x_312_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_size_309_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(lean_object* v_a_354_, lean_object* v_x_355_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_box(0);
return v___x_356_;
}
else
{
lean_object* v_key_357_; lean_object* v_value_358_; lean_object* v_tail_359_; uint8_t v___x_360_; 
v_key_357_ = lean_ctor_get(v_x_355_, 0);
v_value_358_ = lean_ctor_get(v_x_355_, 1);
v_tail_359_ = lean_ctor_get(v_x_355_, 2);
v___x_360_ = lean_expr_eqv(v_key_357_, v_a_354_);
if (v___x_360_ == 0)
{
v_x_355_ = v_tail_359_;
goto _start;
}
else
{
lean_object* v___x_362_; 
lean_inc(v_value_358_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v_value_358_);
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_363_, lean_object* v_x_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_363_, v_x_364_);
lean_dec(v_x_364_);
lean_dec_ref(v_a_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(lean_object* v_m_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_buckets_368_; lean_object* v___x_369_; uint64_t v___x_370_; uint64_t v___x_371_; uint64_t v___x_372_; uint64_t v_fold_373_; uint64_t v___x_374_; uint64_t v___x_375_; uint64_t v___x_376_; size_t v___x_377_; size_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_buckets_368_ = lean_ctor_get(v_m_366_, 1);
v___x_369_ = lean_array_get_size(v_buckets_368_);
v___x_370_ = l_Lean_Expr_hash(v_a_367_);
v___x_371_ = 32ULL;
v___x_372_ = lean_uint64_shift_right(v___x_370_, v___x_371_);
v_fold_373_ = lean_uint64_xor(v___x_370_, v___x_372_);
v___x_374_ = 16ULL;
v___x_375_ = lean_uint64_shift_right(v_fold_373_, v___x_374_);
v___x_376_ = lean_uint64_xor(v_fold_373_, v___x_375_);
v___x_377_ = lean_uint64_to_usize(v___x_376_);
v___x_378_ = lean_usize_of_nat(v___x_369_);
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_sub(v___x_378_, v___x_379_);
v___x_381_ = lean_usize_land(v___x_377_, v___x_380_);
v___x_382_ = lean_array_uget_borrowed(v_buckets_368_, v___x_381_);
v___x_383_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_367_, v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg___boxed(lean_object* v_m_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_384_, v_a_385_);
lean_dec_ref(v_a_385_);
lean_dec_ref(v_m_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(lean_object* v_e_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_op_390_; lean_object* v_exprToVarIndex_391_; lean_object* v_varToExpr_392_; lean_object* v___x_393_; 
v_op_390_ = lean_ctor_get(v_a_388_, 0);
v_exprToVarIndex_391_ = lean_ctor_get(v_a_388_, 1);
v_varToExpr_392_ = lean_ctor_get(v_a_388_, 2);
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_exprToVarIndex_391_, v_e_387_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_405_; 
lean_inc_ref(v_varToExpr_392_);
lean_inc_ref(v_exprToVarIndex_391_);
lean_inc_ref(v_op_390_);
v_isSharedCheck_405_ = !lean_is_exclusive(v_a_388_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; lean_object* v_unused_407_; lean_object* v_unused_408_; 
v_unused_406_ = lean_ctor_get(v_a_388_, 2);
lean_dec(v_unused_406_);
v_unused_407_ = lean_ctor_get(v_a_388_, 1);
lean_dec(v_unused_407_);
v_unused_408_ = lean_ctor_get(v_a_388_, 0);
lean_dec(v_unused_408_);
v___x_395_ = v_a_388_;
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
else
{
lean_dec(v_a_388_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_size_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v_size_397_ = lean_ctor_get(v_exprToVarIndex_391_, 0);
lean_inc_n(v_size_397_, 2);
lean_inc_ref(v_e_387_);
v___x_398_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_exprToVarIndex_391_, v_e_387_, v_size_397_);
v___x_399_ = lean_array_push(v_varToExpr_392_, v_e_387_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 2, v___x_399_);
lean_ctor_set(v___x_395_, 1, v___x_398_);
v___x_401_ = v___x_395_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_op_390_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v___x_399_);
v___x_401_ = v_reuseFailAlloc_404_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_size_397_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
}
else
{
lean_object* v_val_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_417_; 
lean_dec_ref(v_e_387_);
v_val_409_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_417_ == 0)
{
v___x_411_ = v___x_393_;
v_isShared_412_ = v_isSharedCheck_417_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_val_409_);
lean_dec(v___x_393_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_417_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v_val_409_);
lean_ctor_set(v___x_413_, 1, v_a_388_);
if (v_isShared_412_ == 0)
{
lean_ctor_set_tag(v___x_411_, 0);
lean_ctor_set(v___x_411_, 0, v___x_413_);
v___x_415_ = v___x_411_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg___boxed(lean_object* v_e_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_418_, v_a_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(lean_object* v_e_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_422_, v_a_423_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___boxed(lean_object* v_e_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar(v_e_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(lean_object* v_00_u03b2_442_, lean_object* v_m_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___redArg(v_m_443_, v_a_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0___boxed(lean_object* v_00_u03b2_446_, lean_object* v_m_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0(v_00_u03b2_446_, v_m_447_, v_a_448_);
lean_dec_ref(v_a_448_);
lean_dec_ref(v_m_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1(lean_object* v_00_u03b2_450_, lean_object* v_m_451_, lean_object* v_a_452_, lean_object* v_b_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1___redArg(v_m_451_, v_a_452_, v_b_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(lean_object* v_00_u03b2_455_, lean_object* v_a_456_, lean_object* v_x_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___redArg(v_a_456_, v_x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_459_, lean_object* v_a_460_, lean_object* v_x_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__0_spec__0(v_00_u03b2_459_, v_a_460_, v_x_461_);
lean_dec(v_x_461_);
lean_dec_ref(v_a_460_);
return v_res_462_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(lean_object* v_00_u03b2_463_, lean_object* v_a_464_, lean_object* v_x_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___redArg(v_a_464_, v_x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_467_, lean_object* v_a_468_, lean_object* v_x_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__2(v_00_u03b2_467_, v_a_468_, v_x_469_);
lean_dec(v_x_469_);
lean_dec_ref(v_a_468_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3(lean_object* v_00_u03b2_472_, lean_object* v_data_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3___redArg(v_data_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4(lean_object* v_00_u03b2_475_, lean_object* v_a_476_, lean_object* v_b_477_, lean_object* v_x_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__4___redArg(v_a_476_, v_b_477_, v_x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_480_, lean_object* v_i_481_, lean_object* v_source_482_, lean_object* v_target_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4___redArg(v_i_481_, v_source_482_, v_target_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_485_, lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_486_, v_x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(lean_object* v_msgData_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; lean_object* v_env_496_; uint8_t v___x_497_; lean_object* v_env_498_; lean_object* v___x_499_; lean_object* v_toCold_500_; lean_object* v_mctx_501_; lean_object* v_lctx_502_; lean_object* v_options_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_495_ = lean_st_ref_get(v___y_493_);
v_env_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref(v_env_496_);
lean_dec(v___x_495_);
v___x_497_ = 0;
v_env_498_ = l_Lean_Environment_setRecordingDeps(v_env_496_, v___x_497_);
v___x_499_ = lean_st_ref_get(v___y_491_);
v_toCold_500_ = lean_ctor_get(v___y_492_, 0);
v_mctx_501_ = lean_ctor_get(v___x_499_, 0);
lean_inc_ref(v_mctx_501_);
lean_dec(v___x_499_);
v_lctx_502_ = lean_ctor_get(v___y_490_, 2);
v_options_503_ = lean_ctor_get(v_toCold_500_, 2);
lean_inc_ref(v_options_503_);
lean_inc_ref(v_lctx_502_);
v___x_504_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_504_, 0, v_env_498_);
lean_ctor_set(v___x_504_, 1, v_mctx_501_);
lean_ctor_set(v___x_504_, 2, v_lctx_502_);
lean_ctor_set(v___x_504_, 3, v_options_503_);
v___x_505_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_msgData_489_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1___boxed(lean_object* v_msgData_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msgData_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(lean_object* v_msg_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_ref_520_; lean_object* v___x_521_; lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_530_; 
v_ref_520_ = lean_ctor_get(v___y_517_, 2);
v___x_521_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_530_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_530_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_528_; 
lean_inc(v_ref_520_);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v_ref_520_);
lean_ctor_set(v___x_526_, 1, v_a_522_);
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 1);
lean_ctor_set(v___x_524_, 0, v___x_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg___boxed(lean_object* v_msg_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
if (lean_obj_tag(v_a_538_) == 0)
{
lean_object* v___x_540_; 
v___x_540_ = l_List_reverse___redArg(v_a_539_);
return v___x_540_;
}
else
{
lean_object* v_head_541_; lean_object* v_tail_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_551_; 
v_head_541_ = lean_ctor_get(v_a_538_, 0);
v_tail_542_ = lean_ctor_get(v_a_538_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_a_538_);
if (v_isSharedCheck_551_ == 0)
{
v___x_544_ = v_a_538_;
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_tail_542_);
lean_inc(v_head_541_);
lean_dec(v_a_538_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_551_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_546_ = l_Lean_MessageData_ofExpr(v_head_541_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v_a_539_);
lean_ctor_set(v___x_544_, 0, v___x_546_);
v___x_548_ = v___x_544_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_a_539_);
v___x_548_ = v_reuseFailAlloc_550_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
v_a_538_ = v_tail_542_;
v_a_539_ = v___x_548_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__0));
v___x_554_ = l_Lean_stringToMessageData(v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__2));
v___x_557_ = l_Lean_stringToMessageData(v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__4));
v___x_560_ = l_Lean_stringToMessageData(v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(lean_object* v_idx_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_varToExpr_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_varToExpr_570_ = lean_ctor_get(v_a_562_, 2);
v___x_571_ = lean_array_get_size(v_varToExpr_570_);
v___x_572_ = lean_nat_dec_lt(v_idx_561_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
lean_inc_ref(v_varToExpr_570_);
lean_dec_ref(v_a_562_);
v___x_573_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__1);
v___x_574_ = l_Nat_reprFast(v_idx_561_);
v___x_575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
v___x_576_ = l_Lean_MessageData_ofFormat(v___x_575_);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_573_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__3);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Nat_reprFast(v___x_571_);
v___x_581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
v___x_582_ = l_Lean_MessageData_ofFormat(v___x_581_);
v___x_583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_579_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___closed__5);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_array_to_list(v_varToExpr_570_);
v___x_587_ = lean_box(0);
v___x_588_ = l_List_mapTR_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__0(v___x_586_, v___x_587_);
v___x_589_ = l_Lean_MessageData_ofList(v___x_588_);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_585_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v___x_590_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_array_fget(v_varToExpr_570_, v_idx_561_);
lean_dec(v_idx_561_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v_a_562_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr___boxed(lean_object* v_idx_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr(v_idx_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(lean_object* v_00_u03b1_605_, lean_object* v_msg_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___redArg(v_msg_606_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1___boxed(lean_object* v_00_u03b1_616_, lean_object* v_msg_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1(v_00_u03b1_616_, v_msg_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(lean_object* v_c_627_){
_start:
{
lean_object* v___y_629_; 
if (lean_obj_tag(v_c_627_) == 0)
{
lean_object* v___x_633_; 
v___x_633_ = lean_unsigned_to_nat(0u);
v___y_629_ = v___x_633_;
goto v___jp_628_;
}
else
{
lean_object* v_val_634_; 
v_val_634_ = lean_ctor_get(v_c_627_, 0);
v___y_629_ = v_val_634_;
goto v___jp_628_;
}
v___jp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_add(v___y_629_, v___x_630_);
v___x_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0___boxed(lean_object* v_c_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v_c_635_);
lean_dec(v_c_635_);
return v_res_636_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_box(0);
v___x_638_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(lean_object* v_a_639_, lean_object* v_x_640_){
_start:
{
if (lean_obj_tag(v_x_640_) == 0)
{
lean_object* v___x_641_; lean_object* v_val_642_; lean_object* v___x_643_; 
v___x_641_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___closed__0);
v_val_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_val_642_);
v___x_643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_643_, 0, v_a_639_);
lean_ctor_set(v___x_643_, 1, v_val_642_);
lean_ctor_set(v___x_643_, 2, v_x_640_);
return v___x_643_;
}
else
{
lean_object* v_key_644_; lean_object* v_value_645_; lean_object* v_tail_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_661_; 
v_key_644_ = lean_ctor_get(v_x_640_, 0);
v_value_645_ = lean_ctor_get(v_x_640_, 1);
v_tail_646_ = lean_ctor_get(v_x_640_, 2);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_640_);
if (v_isSharedCheck_661_ == 0)
{
v___x_648_ = v_x_640_;
v_isShared_649_ = v_isSharedCheck_661_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_tail_646_);
lean_inc(v_value_645_);
lean_inc(v_key_644_);
lean_dec(v_x_640_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_661_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
uint8_t v___x_650_; 
v___x_650_ = lean_nat_dec_eq(v_key_644_, v_a_639_);
if (v___x_650_ == 0)
{
lean_object* v_tail_651_; lean_object* v___x_653_; 
v_tail_651_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_639_, v_tail_646_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 2, v_tail_651_);
v___x_653_ = v___x_648_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_key_644_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_value_645_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_tail_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_val_657_; lean_object* v___x_659_; 
lean_dec(v_key_644_);
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v_value_645_);
v___x_656_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2___lam__0(v___x_655_);
lean_dec_ref_known(v___x_655_, 1);
v_val_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_val_657_);
lean_dec(v___x_656_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v_val_657_);
lean_ctor_set(v___x_648_, 0, v_a_639_);
v___x_659_ = v___x_648_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_639_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_val_657_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_tail_646_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
if (lean_obj_tag(v_x_663_) == 0)
{
return v_x_662_;
}
else
{
lean_object* v_key_664_; lean_object* v_value_665_; lean_object* v_tail_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_689_; 
v_key_664_ = lean_ctor_get(v_x_663_, 0);
v_value_665_ = lean_ctor_get(v_x_663_, 1);
v_tail_666_ = lean_ctor_get(v_x_663_, 2);
v_isSharedCheck_689_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_689_ == 0)
{
v___x_668_ = v_x_663_;
v_isShared_669_ = v_isSharedCheck_689_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_tail_666_);
lean_inc(v_value_665_);
lean_inc(v_key_664_);
lean_dec(v_x_663_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_689_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; uint64_t v___x_671_; uint64_t v___x_672_; uint64_t v___x_673_; uint64_t v_fold_674_; uint64_t v___x_675_; uint64_t v___x_676_; uint64_t v___x_677_; size_t v___x_678_; size_t v___x_679_; size_t v___x_680_; size_t v___x_681_; size_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_670_ = lean_array_get_size(v_x_662_);
v___x_671_ = lean_uint64_of_nat(v_key_664_);
v___x_672_ = 32ULL;
v___x_673_ = lean_uint64_shift_right(v___x_671_, v___x_672_);
v_fold_674_ = lean_uint64_xor(v___x_671_, v___x_673_);
v___x_675_ = 16ULL;
v___x_676_ = lean_uint64_shift_right(v_fold_674_, v___x_675_);
v___x_677_ = lean_uint64_xor(v_fold_674_, v___x_676_);
v___x_678_ = lean_uint64_to_usize(v___x_677_);
v___x_679_ = lean_usize_of_nat(v___x_670_);
v___x_680_ = ((size_t)1ULL);
v___x_681_ = lean_usize_sub(v___x_679_, v___x_680_);
v___x_682_ = lean_usize_land(v___x_678_, v___x_681_);
v___x_683_ = lean_array_uget_borrowed(v_x_662_, v___x_682_);
lean_inc(v___x_683_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 2, v___x_683_);
v___x_685_ = v___x_668_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_key_664_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_value_665_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v___x_683_);
v___x_685_ = v_reuseFailAlloc_688_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; 
v___x_686_ = lean_array_uset(v_x_662_, v___x_682_, v___x_685_);
v_x_662_ = v___x_686_;
v_x_663_ = v_tail_666_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_690_, lean_object* v_source_691_, lean_object* v_target_692_){
_start:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_array_get_size(v_source_691_);
v___x_694_ = lean_nat_dec_lt(v_i_690_, v___x_693_);
if (v___x_694_ == 0)
{
lean_dec_ref(v_source_691_);
lean_dec(v_i_690_);
return v_target_692_;
}
else
{
lean_object* v_es_695_; lean_object* v___x_696_; lean_object* v_source_697_; lean_object* v_target_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_es_695_ = lean_array_fget(v_source_691_, v_i_690_);
v___x_696_ = lean_box(0);
v_source_697_ = lean_array_fset(v_source_691_, v_i_690_, v___x_696_);
v_target_698_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_692_, v_es_695_);
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_nat_add(v_i_690_, v___x_699_);
lean_dec(v_i_690_);
v_i_690_ = v___x_700_;
v_source_691_ = v_source_697_;
v_target_692_ = v_target_698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(lean_object* v_data_702_){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_nbuckets_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_703_ = lean_array_get_size(v_data_702_);
v___x_704_ = lean_unsigned_to_nat(2u);
v_nbuckets_705_ = lean_nat_mul(v___x_703_, v___x_704_);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_box(0);
v___x_708_ = lean_mk_array(v_nbuckets_705_, v___x_707_);
v___x_709_ = lean_array_propagate_mark(v_data_702_, v___x_708_);
v___x_710_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v___x_706_, v_data_702_, v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(lean_object* v_a_711_, lean_object* v_x_712_){
_start:
{
if (lean_obj_tag(v_x_712_) == 0)
{
uint8_t v___x_713_; 
v___x_713_ = 0;
return v___x_713_;
}
else
{
lean_object* v_key_714_; lean_object* v_tail_715_; uint8_t v___x_716_; 
v_key_714_ = lean_ctor_get(v_x_712_, 0);
v_tail_715_ = lean_ctor_get(v_x_712_, 2);
v___x_716_ = lean_nat_dec_eq(v_key_714_, v_a_711_);
if (v___x_716_ == 0)
{
v_x_712_ = v_tail_715_;
goto _start;
}
else
{
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_718_, lean_object* v_x_719_){
_start:
{
uint8_t v_res_720_; lean_object* v_r_721_; 
v_res_720_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_718_, v_x_719_);
lean_dec(v_x_719_);
lean_dec(v_a_718_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(lean_object* v_m_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_size_724_; lean_object* v_buckets_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_773_; 
v_size_724_ = lean_ctor_get(v_m_722_, 0);
v_buckets_725_ = lean_ctor_get(v_m_722_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_m_722_);
if (v_isSharedCheck_773_ == 0)
{
v___x_727_ = v_m_722_;
v_isShared_728_ = v_isSharedCheck_773_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_buckets_725_);
lean_inc(v_size_724_);
lean_dec(v_m_722_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_773_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; uint64_t v___x_730_; uint64_t v___x_731_; uint64_t v___x_732_; uint64_t v_fold_733_; uint64_t v___x_734_; uint64_t v___x_735_; uint64_t v___x_736_; size_t v___x_737_; size_t v___x_738_; size_t v___x_739_; size_t v___x_740_; size_t v___x_741_; lean_object* v_bkt_742_; uint8_t v___x_743_; 
v___x_729_ = lean_array_get_size(v_buckets_725_);
v___x_730_ = lean_uint64_of_nat(v_a_723_);
v___x_731_ = 32ULL;
v___x_732_ = lean_uint64_shift_right(v___x_730_, v___x_731_);
v_fold_733_ = lean_uint64_xor(v___x_730_, v___x_732_);
v___x_734_ = 16ULL;
v___x_735_ = lean_uint64_shift_right(v_fold_733_, v___x_734_);
v___x_736_ = lean_uint64_xor(v_fold_733_, v___x_735_);
v___x_737_ = lean_uint64_to_usize(v___x_736_);
v___x_738_ = lean_usize_of_nat(v___x_729_);
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_sub(v___x_738_, v___x_739_);
v___x_741_ = lean_usize_land(v___x_737_, v___x_740_);
v_bkt_742_ = lean_array_uget_borrowed(v_buckets_725_, v___x_741_);
v___x_743_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_723_, v_bkt_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v_size_x27_745_; lean_object* v___x_746_; lean_object* v_buckets_x27_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_744_ = lean_unsigned_to_nat(1u);
v_size_x27_745_ = lean_nat_add(v_size_724_, v___x_744_);
lean_dec(v_size_724_);
lean_inc(v_bkt_742_);
v___x_746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_746_, 0, v_a_723_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
lean_ctor_set(v___x_746_, 2, v_bkt_742_);
v_buckets_x27_747_ = lean_array_uset(v_buckets_725_, v___x_741_, v___x_746_);
v___x_748_ = lean_unsigned_to_nat(4u);
v___x_749_ = lean_nat_mul(v_size_x27_745_, v___x_748_);
v___x_750_ = lean_unsigned_to_nat(3u);
v___x_751_ = lean_nat_div(v___x_749_, v___x_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_array_get_size(v_buckets_x27_747_);
v___x_753_ = lean_nat_dec_le(v___x_751_, v___x_752_);
lean_dec(v___x_751_);
if (v___x_753_ == 0)
{
lean_object* v_val_754_; lean_object* v___x_756_; 
v_val_754_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_747_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_val_754_);
lean_ctor_set(v___x_727_, 0, v_size_x27_745_);
v___x_756_ = v___x_727_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_size_x27_745_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_val_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
else
{
lean_object* v___x_759_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_buckets_x27_747_);
lean_ctor_set(v___x_727_, 0, v_size_x27_745_);
v___x_759_ = v___x_727_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_size_x27_745_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_buckets_x27_747_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
else
{
lean_object* v___x_761_; lean_object* v_buckets_x27_762_; lean_object* v_bkt_x27_763_; lean_object* v___y_765_; uint8_t v___x_770_; 
lean_inc(v_bkt_742_);
v___x_761_ = lean_box(0);
v_buckets_x27_762_ = lean_array_uset(v_buckets_725_, v___x_741_, v___x_761_);
lean_inc(v_a_723_);
v_bkt_x27_763_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__2(v_a_723_, v_bkt_742_);
v___x_770_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_723_, v_bkt_x27_763_);
lean_dec(v_a_723_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_sub(v_size_724_, v___x_771_);
lean_dec(v_size_724_);
v___y_765_ = v___x_772_;
goto v___jp_764_;
}
else
{
v___y_765_ = v_size_724_;
goto v___jp_764_;
}
v___jp_764_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_array_uset(v_buckets_x27_762_, v___x_741_, v_bkt_x27_763_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v___x_766_);
lean_ctor_set(v___x_727_, 0, v___y_765_);
v___x_768_ = v___x_727_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___y_765_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(lean_object* v_coeff_774_, lean_object* v_e_775_, lean_object* v_a_776_){
_start:
{
lean_object* v___x_778_; lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_796_; 
v___x_778_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_exprToVar___redArg(v_e_775_, v_a_776_);
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_796_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_796_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_796_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_fst_783_; lean_object* v_snd_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_795_; 
v_fst_783_ = lean_ctor_get(v_a_779_, 0);
v_snd_784_ = lean_ctor_get(v_a_779_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_a_779_);
if (v_isSharedCheck_795_ == 0)
{
v___x_786_ = v_a_779_;
v_isShared_787_ = v_isSharedCheck_795_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_snd_784_);
lean_inc(v_fst_783_);
lean_dec(v_a_779_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_795_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0(v_coeff_774_, v_fst_783_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_788_);
v___x_790_ = v___x_786_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_snd_784_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_790_);
v___x_792_ = v___x_781_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg___boxed(lean_object* v_coeff_797_, lean_object* v_e_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_797_, v_e_798_, v_a_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(lean_object* v_coeff_802_, lean_object* v_e_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_802_, v_e_803_, v_a_804_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___boxed(lean_object* v_coeff_813_, lean_object* v_e_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar(v_coeff_813_, v_e_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
return v_res_823_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(lean_object* v_00_u03b2_824_, lean_object* v_a_825_, lean_object* v_x_826_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_825_, v_x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_828_, lean_object* v_a_829_, lean_object* v_x_830_){
_start:
{
uint8_t v_res_831_; lean_object* v_r_832_; 
v_res_831_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0(v_00_u03b2_828_, v_a_829_, v_x_830_);
lean_dec(v_x_830_);
lean_dec(v_a_829_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1(lean_object* v_00_u03b2_833_, lean_object* v_data_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_data_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_836_, lean_object* v_i_837_, lean_object* v_source_838_, lean_object* v_target_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2___redArg(v_i_837_, v_source_838_, v_target_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_841_, lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_842_, v_x_843_);
return v___x_844_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_845_; double v___x_846_; 
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_float_of_nat(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(lean_object* v_cls_850_, lean_object* v_msg_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_ref_858_; lean_object* v___x_859_; lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_906_; 
v_ref_858_ = lean_ctor_get(v___y_855_, 2);
v___x_859_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_851_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_906_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_906_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_906_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v_traceState_865_; lean_object* v_env_866_; lean_object* v_nextMacroScope_867_; lean_object* v_ngen_868_; lean_object* v_auxDeclNGen_869_; lean_object* v_cache_870_; lean_object* v_recordedDeps_871_; lean_object* v_messages_872_; lean_object* v_infoState_873_; lean_object* v_snapshotTasks_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_905_; 
v___x_864_ = lean_st_ref_take(v___y_856_);
v_traceState_865_ = lean_ctor_get(v___x_864_, 4);
v_env_866_ = lean_ctor_get(v___x_864_, 0);
v_nextMacroScope_867_ = lean_ctor_get(v___x_864_, 1);
v_ngen_868_ = lean_ctor_get(v___x_864_, 2);
v_auxDeclNGen_869_ = lean_ctor_get(v___x_864_, 3);
v_cache_870_ = lean_ctor_get(v___x_864_, 5);
v_recordedDeps_871_ = lean_ctor_get(v___x_864_, 6);
v_messages_872_ = lean_ctor_get(v___x_864_, 7);
v_infoState_873_ = lean_ctor_get(v___x_864_, 8);
v_snapshotTasks_874_ = lean_ctor_get(v___x_864_, 9);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_905_ == 0)
{
v___x_876_ = v___x_864_;
v_isShared_877_ = v_isSharedCheck_905_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_snapshotTasks_874_);
lean_inc(v_infoState_873_);
lean_inc(v_messages_872_);
lean_inc(v_recordedDeps_871_);
lean_inc(v_cache_870_);
lean_inc(v_traceState_865_);
lean_inc(v_auxDeclNGen_869_);
lean_inc(v_ngen_868_);
lean_inc(v_nextMacroScope_867_);
lean_inc(v_env_866_);
lean_dec(v___x_864_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_905_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
uint64_t v_tid_878_; lean_object* v_traces_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_904_; 
v_tid_878_ = lean_ctor_get_uint64(v_traceState_865_, sizeof(void*)*1);
v_traces_879_ = lean_ctor_get(v_traceState_865_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v_traceState_865_);
if (v_isSharedCheck_904_ == 0)
{
v___x_881_ = v_traceState_865_;
v_isShared_882_ = v_isSharedCheck_904_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_traces_879_);
lean_dec(v_traceState_865_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_904_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; double v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_883_ = lean_box(0);
v___x_884_ = lean_box(0);
v___x_885_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_886_ = 0;
v___x_887_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_888_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_888_, 0, v_cls_850_);
lean_ctor_set(v___x_888_, 1, v___x_884_);
lean_ctor_set(v___x_888_, 2, v___x_887_);
lean_ctor_set_float(v___x_888_, sizeof(void*)*3, v___x_885_);
lean_ctor_set_float(v___x_888_, sizeof(void*)*3 + 8, v___x_885_);
lean_ctor_set_uint8(v___x_888_, sizeof(void*)*3 + 16, v___x_886_);
v___x_889_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_890_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v_a_860_);
lean_ctor_set(v___x_890_, 2, v___x_889_);
lean_inc(v_ref_858_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_ref_858_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_PersistentArray_push___redArg(v_traces_879_, v___x_891_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_892_);
v___x_894_ = v___x_881_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_892_);
lean_ctor_set_uint64(v_reuseFailAlloc_903_, sizeof(void*)*1, v_tid_878_);
v___x_894_ = v_reuseFailAlloc_903_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 4, v___x_894_);
v___x_896_ = v___x_876_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_env_866_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_nextMacroScope_867_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_ngen_868_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_auxDeclNGen_869_);
lean_ctor_set(v_reuseFailAlloc_902_, 4, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_902_, 5, v_cache_870_);
lean_ctor_set(v_reuseFailAlloc_902_, 6, v_recordedDeps_871_);
lean_ctor_set(v_reuseFailAlloc_902_, 7, v_messages_872_);
lean_ctor_set(v_reuseFailAlloc_902_, 8, v_infoState_873_);
lean_ctor_set(v_reuseFailAlloc_902_, 9, v_snapshotTasks_874_);
v___x_896_ = v_reuseFailAlloc_902_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_897_ = lean_st_ref_put(v___y_856_, v___x_896_);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_883_);
lean_ctor_set(v___x_898_, 1, v___y_852_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_898_);
v___x_900_ = v___x_862_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___boxed(lean_object* v_cls_907_, lean_object* v_msg_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_907_, v_msg_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
return v_res_915_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6(void){
_start:
{
lean_object* v_cls_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_cls_926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_928_ = l_Lean_Name_append(v___x_927_, v_cls_926_);
return v___x_928_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__7));
v___x_931_ = l_Lean_stringToMessageData(v___x_930_);
return v___x_931_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__9));
v___x_934_ = l_Lean_stringToMessageData(v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__11));
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__13));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(lean_object* v_op_941_, lean_object* v_coeff_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
if (lean_obj_tag(v_a_943_) == 5)
{
lean_object* v_fn_952_; 
v_fn_952_ = lean_ctor_get(v_a_943_, 0);
if (lean_obj_tag(v_fn_952_) == 5)
{
lean_object* v_arg_953_; lean_object* v_fn_954_; lean_object* v_arg_955_; uint8_t v___x_956_; 
v_arg_953_ = lean_ctor_get(v_a_943_, 1);
v_fn_954_ = lean_ctor_get(v_fn_952_, 0);
v_arg_955_ = lean_ctor_get(v_fn_952_, 1);
v___x_956_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_isSameKind___redArg(v_fn_954_);
if (v___x_956_ == 0)
{
lean_object* v_toCold_957_; lean_object* v_options_958_; uint8_t v_hasTrace_959_; 
v_toCold_957_ = lean_ctor_get(v_a_949_, 0);
v_options_958_ = lean_ctor_get(v_toCold_957_, 2);
v_hasTrace_959_ = lean_ctor_get_uint8(v_options_958_, sizeof(void*)*1);
if (v_hasTrace_959_ == 0)
{
lean_object* v___x_960_; 
lean_dec_ref(v_op_941_);
v___x_960_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_942_, v_a_943_, v_a_944_);
return v___x_960_;
}
else
{
lean_object* v_inheritedTraceOptions_961_; lean_object* v_cls_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_inheritedTraceOptions_961_ = lean_ctor_get(v_toCold_957_, 11);
v_cls_962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_964_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_961_, v_options_958_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; 
lean_dec_ref(v_op_941_);
v___x_965_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_942_, v_a_943_, v_a_944_);
return v___x_965_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_966_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__8);
lean_inc_ref(v_fn_954_);
v___x_967_ = l_Lean_MessageData_ofExpr(v_fn_954_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__10);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
lean_inc_ref(v_arg_955_);
v___x_971_ = l_Lean_MessageData_ofExpr(v_arg_955_);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_969_);
lean_inc_ref(v_arg_953_);
v___x_974_ = l_Lean_MessageData_ofExpr(v_arg_953_);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__12);
v___x_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_941_);
v___x_979_ = l_Lean_MessageData_ofExpr(v___x_978_);
v___x_980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_977_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__14);
v___x_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_962_, v___x_982_, v_a_944_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_snd_985_; lean_object* v___x_986_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v_snd_985_ = lean_ctor_get(v_a_984_, 1);
lean_inc(v_snd_985_);
lean_dec(v_a_984_);
v___x_986_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_942_, v_a_943_, v_snd_985_);
return v___x_986_;
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref_known(v_a_943_, 2);
lean_dec_ref(v_coeff_942_);
v_a_987_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_983_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_983_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
}
else
{
lean_object* v___x_995_; 
lean_inc_ref(v_arg_955_);
lean_inc_ref(v_arg_953_);
lean_dec_ref_known(v_a_943_, 2);
lean_inc_ref(v_op_941_);
v___x_995_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_941_, v_coeff_942_, v_arg_955_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v_fst_997_; lean_object* v_snd_998_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v_fst_997_ = lean_ctor_get(v_a_996_, 0);
lean_inc(v_fst_997_);
v_snd_998_ = lean_ctor_get(v_a_996_, 1);
lean_inc(v_snd_998_);
lean_dec(v_a_996_);
v_coeff_942_ = v_fst_997_;
v_a_943_ = v_arg_953_;
v_a_944_ = v_snd_998_;
goto _start;
}
else
{
lean_dec_ref(v_arg_953_);
lean_dec_ref(v_op_941_);
return v___x_995_;
}
}
}
else
{
lean_object* v___x_1000_; 
lean_dec_ref(v_op_941_);
v___x_1000_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_942_, v_a_943_, v_a_944_);
return v___x_1000_;
}
}
else
{
lean_object* v___x_1001_; 
lean_dec_ref(v_op_941_);
v___x_1001_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar___redArg(v_coeff_942_, v_a_943_, v_a_944_);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___boxed(lean_object* v_op_1002_, lean_object* v_coeff_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1002_, v_coeff_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(lean_object* v_cls_1014_, lean_object* v_msg_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg(v_cls_1014_, v_msg_1015_, v___y_1016_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___boxed(lean_object* v_cls_1025_, lean_object* v_msg_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0(v_cls_1025_, v_msg_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1035_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = lean_box(0);
v___x_1037_ = lean_unsigned_to_nat(16u);
v___x_1038_ = lean_mk_array(v___x_1037_, v___x_1036_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v___x_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(lean_object* v_op_1042_, lean_object* v_e_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1053_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go(v_op_1042_, v___x_1052_, v_e_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___boxed(lean_object* v_op_1054_, lean_object* v_e_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_op_1054_, v_e_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(lean_object* v_a_1065_, lean_object* v_x_1066_){
_start:
{
if (lean_obj_tag(v_x_1066_) == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_box(0);
return v___x_1067_;
}
else
{
lean_object* v_key_1068_; lean_object* v_value_1069_; lean_object* v_tail_1070_; uint8_t v___x_1071_; 
v_key_1068_ = lean_ctor_get(v_x_1066_, 0);
v_value_1069_ = lean_ctor_get(v_x_1066_, 1);
v_tail_1070_ = lean_ctor_get(v_x_1066_, 2);
v___x_1071_ = lean_nat_dec_eq(v_key_1068_, v_a_1065_);
if (v___x_1071_ == 0)
{
v_x_1066_ = v_tail_1070_;
goto _start;
}
else
{
lean_object* v___x_1073_; 
lean_inc(v_value_1069_);
v___x_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1073_, 0, v_value_1069_);
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg___boxed(lean_object* v_a_1074_, lean_object* v_x_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1074_, v_x_1075_);
lean_dec(v_x_1075_);
lean_dec(v_a_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(lean_object* v_m_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_buckets_1079_; lean_object* v___x_1080_; uint64_t v___x_1081_; uint64_t v___x_1082_; uint64_t v___x_1083_; uint64_t v_fold_1084_; uint64_t v___x_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_buckets_1079_ = lean_ctor_get(v_m_1077_, 1);
v___x_1080_ = lean_array_get_size(v_buckets_1079_);
v___x_1081_ = lean_uint64_of_nat(v_a_1078_);
v___x_1082_ = 32ULL;
v___x_1083_ = lean_uint64_shift_right(v___x_1081_, v___x_1082_);
v_fold_1084_ = lean_uint64_xor(v___x_1081_, v___x_1083_);
v___x_1085_ = 16ULL;
v___x_1086_ = lean_uint64_shift_right(v_fold_1084_, v___x_1085_);
v___x_1087_ = lean_uint64_xor(v_fold_1084_, v___x_1086_);
v___x_1088_ = lean_uint64_to_usize(v___x_1087_);
v___x_1089_ = lean_usize_of_nat(v___x_1080_);
v___x_1090_ = ((size_t)1ULL);
v___x_1091_ = lean_usize_sub(v___x_1089_, v___x_1090_);
v___x_1092_ = lean_usize_land(v___x_1088_, v___x_1091_);
v___x_1093_ = lean_array_uget_borrowed(v_buckets_1079_, v___x_1092_);
v___x_1094_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1078_, v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg___boxed(lean_object* v_m_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1095_, v_a_1096_);
lean_dec(v_a_1096_);
lean_dec_ref(v_m_1095_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(lean_object* v_a_1098_, lean_object* v_b_1099_, lean_object* v_x_1100_){
_start:
{
if (lean_obj_tag(v_x_1100_) == 0)
{
lean_dec(v_b_1099_);
lean_dec(v_a_1098_);
return v_x_1100_;
}
else
{
lean_object* v_key_1101_; lean_object* v_value_1102_; lean_object* v_tail_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1115_; 
v_key_1101_ = lean_ctor_get(v_x_1100_, 0);
v_value_1102_ = lean_ctor_get(v_x_1100_, 1);
v_tail_1103_ = lean_ctor_get(v_x_1100_, 2);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1105_ = v_x_1100_;
v_isShared_1106_ = v_isSharedCheck_1115_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_tail_1103_);
lean_inc(v_value_1102_);
lean_inc(v_key_1101_);
lean_dec(v_x_1100_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1115_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
uint8_t v___x_1107_; 
v___x_1107_ = lean_nat_dec_eq(v_key_1101_, v_a_1098_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1098_, v_b_1099_, v_tail_1103_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 2, v___x_1108_);
v___x_1110_ = v___x_1105_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_key_1101_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_value_1102_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
else
{
lean_object* v___x_1113_; 
lean_dec(v_value_1102_);
lean_dec(v_key_1101_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 1, v_b_1099_);
lean_ctor_set(v___x_1105_, 0, v_a_1098_);
v___x_1113_ = v___x_1105_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1098_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_b_1099_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_tail_1103_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(lean_object* v_m_1116_, lean_object* v_a_1117_, lean_object* v_b_1118_){
_start:
{
lean_object* v_size_1119_; lean_object* v_buckets_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1163_; 
v_size_1119_ = lean_ctor_get(v_m_1116_, 0);
v_buckets_1120_ = lean_ctor_get(v_m_1116_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_m_1116_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1122_ = v_m_1116_;
v_isShared_1123_ = v_isSharedCheck_1163_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_buckets_1120_);
lean_inc(v_size_1119_);
lean_dec(v_m_1116_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1163_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; uint64_t v___x_1125_; uint64_t v___x_1126_; uint64_t v___x_1127_; uint64_t v_fold_1128_; uint64_t v___x_1129_; uint64_t v___x_1130_; uint64_t v___x_1131_; size_t v___x_1132_; size_t v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; size_t v___x_1136_; lean_object* v_bkt_1137_; uint8_t v___x_1138_; 
v___x_1124_ = lean_array_get_size(v_buckets_1120_);
v___x_1125_ = lean_uint64_of_nat(v_a_1117_);
v___x_1126_ = 32ULL;
v___x_1127_ = lean_uint64_shift_right(v___x_1125_, v___x_1126_);
v_fold_1128_ = lean_uint64_xor(v___x_1125_, v___x_1127_);
v___x_1129_ = 16ULL;
v___x_1130_ = lean_uint64_shift_right(v_fold_1128_, v___x_1129_);
v___x_1131_ = lean_uint64_xor(v_fold_1128_, v___x_1130_);
v___x_1132_ = lean_uint64_to_usize(v___x_1131_);
v___x_1133_ = lean_usize_of_nat(v___x_1124_);
v___x_1134_ = ((size_t)1ULL);
v___x_1135_ = lean_usize_sub(v___x_1133_, v___x_1134_);
v___x_1136_ = lean_usize_land(v___x_1132_, v___x_1135_);
v_bkt_1137_ = lean_array_uget_borrowed(v_buckets_1120_, v___x_1136_);
v___x_1138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1117_, v_bkt_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v_size_x27_1140_; lean_object* v___x_1141_; lean_object* v_buckets_x27_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1139_ = lean_unsigned_to_nat(1u);
v_size_x27_1140_ = lean_nat_add(v_size_1119_, v___x_1139_);
lean_dec(v_size_1119_);
lean_inc(v_bkt_1137_);
v___x_1141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1141_, 0, v_a_1117_);
lean_ctor_set(v___x_1141_, 1, v_b_1118_);
lean_ctor_set(v___x_1141_, 2, v_bkt_1137_);
v_buckets_x27_1142_ = lean_array_uset(v_buckets_1120_, v___x_1136_, v___x_1141_);
v___x_1143_ = lean_unsigned_to_nat(4u);
v___x_1144_ = lean_nat_mul(v_size_x27_1140_, v___x_1143_);
v___x_1145_ = lean_unsigned_to_nat(3u);
v___x_1146_ = lean_nat_div(v___x_1144_, v___x_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_array_get_size(v_buckets_x27_1142_);
v___x_1148_ = lean_nat_dec_le(v___x_1146_, v___x_1147_);
lean_dec(v___x_1146_);
if (v___x_1148_ == 0)
{
lean_object* v_val_1149_; lean_object* v___x_1151_; 
v_val_1149_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__1___redArg(v_buckets_x27_1142_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v_val_1149_);
lean_ctor_set(v___x_1122_, 0, v_size_x27_1140_);
v___x_1151_ = v___x_1122_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_size_x27_1140_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_val_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
else
{
lean_object* v___x_1154_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v_buckets_x27_1142_);
lean_ctor_set(v___x_1122_, 0, v_size_x27_1140_);
v___x_1154_ = v___x_1122_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_size_x27_1140_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_buckets_x27_1142_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
else
{
lean_object* v___x_1156_; lean_object* v_buckets_x27_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_inc(v_bkt_1137_);
v___x_1156_ = lean_box(0);
v_buckets_x27_1157_ = lean_array_uset(v_buckets_1120_, v___x_1136_, v___x_1156_);
v___x_1158_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1117_, v_b_1118_, v_bkt_1137_);
v___x_1159_ = lean_array_uset(v_buckets_x27_1157_, v___x_1136_, v___x_1158_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v___x_1159_);
v___x_1161_ = v___x_1122_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_size_1119_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(lean_object* v_snd_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_){
_start:
{
if (lean_obj_tag(v_x_1166_) == 0)
{
return v_x_1165_;
}
else
{
lean_object* v_key_1167_; lean_object* v_value_1168_; lean_object* v_tail_1169_; lean_object* v___y_1171_; lean_object* v___x_1174_; 
v_key_1167_ = lean_ctor_get(v_x_1166_, 0);
lean_inc(v_key_1167_);
v_value_1168_ = lean_ctor_get(v_x_1166_, 1);
lean_inc(v_value_1168_);
v_tail_1169_ = lean_ctor_get(v_x_1166_, 2);
lean_inc(v_tail_1169_);
lean_dec_ref_known(v_x_1166_, 3);
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_snd_1164_, v_key_1167_);
if (lean_obj_tag(v___x_1174_) == 1)
{
lean_object* v_val_1175_; uint8_t v___x_1176_; 
v_val_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_val_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = lean_nat_dec_le(v_value_1168_, v_val_1175_);
if (v___x_1176_ == 0)
{
lean_dec(v_value_1168_);
v___y_1171_ = v_val_1175_;
goto v___jp_1170_;
}
else
{
lean_dec(v_val_1175_);
v___y_1171_ = v_value_1168_;
goto v___jp_1170_;
}
}
else
{
lean_dec(v___x_1174_);
lean_dec(v_value_1168_);
lean_dec(v_key_1167_);
v_x_1166_ = v_tail_1169_;
goto _start;
}
v___jp_1170_:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_x_1165_, v_key_1167_, v___y_1171_);
v_x_1165_ = v___x_1172_;
v_x_1166_ = v_tail_1169_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5___boxed(lean_object* v_snd_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1178_, v_x_1179_, v_x_1180_);
lean_dec_ref(v_snd_1178_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(lean_object* v_snd_1182_, lean_object* v_as_1183_, size_t v_i_1184_, size_t v_stop_1185_, lean_object* v_b_1186_){
_start:
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_usize_dec_eq(v_i_1184_, v_stop_1185_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; 
v___x_1188_ = lean_array_uget_borrowed(v_as_1183_, v_i_1184_);
lean_inc(v___x_1188_);
v___x_1189_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__5(v_snd_1182_, v_b_1186_, v___x_1188_);
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_add(v_i_1184_, v___x_1190_);
v_i_1184_ = v___x_1191_;
v_b_1186_ = v___x_1189_;
goto _start;
}
else
{
return v_b_1186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6___boxed(lean_object* v_snd_1193_, lean_object* v_as_1194_, lean_object* v_i_1195_, lean_object* v_stop_1196_, lean_object* v_b_1197_){
_start:
{
size_t v_i_boxed_1198_; size_t v_stop_boxed_1199_; lean_object* v_res_1200_; 
v_i_boxed_1198_ = lean_unbox_usize(v_i_1195_);
lean_dec(v_i_1195_);
v_stop_boxed_1199_ = lean_unbox_usize(v_stop_1196_);
lean_dec(v_stop_1196_);
v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1193_, v_as_1194_, v_i_boxed_1198_, v_stop_boxed_1199_, v_b_1197_);
lean_dec_ref(v_as_1194_);
lean_dec_ref(v_snd_1193_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(lean_object* v_commonCnt_1201_, lean_object* v_a_1202_, lean_object* v_x_1203_){
_start:
{
if (lean_obj_tag(v_x_1203_) == 0)
{
lean_dec(v_a_1202_);
return v_x_1203_;
}
else
{
lean_object* v_key_1204_; lean_object* v_value_1205_; lean_object* v_tail_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1219_; 
v_key_1204_ = lean_ctor_get(v_x_1203_, 0);
v_value_1205_ = lean_ctor_get(v_x_1203_, 1);
v_tail_1206_ = lean_ctor_get(v_x_1203_, 2);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_x_1203_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1208_ = v_x_1203_;
v_isShared_1209_ = v_isSharedCheck_1219_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_tail_1206_);
lean_inc(v_value_1205_);
lean_inc(v_key_1204_);
lean_dec(v_x_1203_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1219_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_nat_dec_eq(v_key_1204_, v_a_1202_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1201_, v_a_1202_, v_tail_1206_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 2, v___x_1211_);
v___x_1213_ = v___x_1208_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_key_1204_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_value_1205_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
lean_dec(v_key_1204_);
v___x_1215_ = lean_nat_sub(v_value_1205_, v_commonCnt_1201_);
lean_dec(v_value_1205_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 1, v___x_1215_);
lean_ctor_set(v___x_1208_, 0, v_a_1202_);
v___x_1217_ = v___x_1208_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1202_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v_tail_1206_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0___boxed(lean_object* v_commonCnt_1220_, lean_object* v_a_1221_, lean_object* v_x_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1220_, v_a_1221_, v_x_1222_);
lean_dec(v_commonCnt_1220_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(lean_object* v_commonCnt_1224_, lean_object* v_m_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_size_1227_; lean_object* v_buckets_1228_; lean_object* v___x_1229_; uint64_t v___x_1230_; uint64_t v___x_1231_; uint64_t v___x_1232_; uint64_t v_fold_1233_; uint64_t v___x_1234_; uint64_t v___x_1235_; uint64_t v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; lean_object* v_bucket_1242_; uint8_t v___x_1243_; 
v_size_1227_ = lean_ctor_get(v_m_1225_, 0);
v_buckets_1228_ = lean_ctor_get(v_m_1225_, 1);
v___x_1229_ = lean_array_get_size(v_buckets_1228_);
v___x_1230_ = lean_uint64_of_nat(v_a_1226_);
v___x_1231_ = 32ULL;
v___x_1232_ = lean_uint64_shift_right(v___x_1230_, v___x_1231_);
v_fold_1233_ = lean_uint64_xor(v___x_1230_, v___x_1232_);
v___x_1234_ = 16ULL;
v___x_1235_ = lean_uint64_shift_right(v_fold_1233_, v___x_1234_);
v___x_1236_ = lean_uint64_xor(v_fold_1233_, v___x_1235_);
v___x_1237_ = lean_uint64_to_usize(v___x_1236_);
v___x_1238_ = lean_usize_of_nat(v___x_1229_);
v___x_1239_ = ((size_t)1ULL);
v___x_1240_ = lean_usize_sub(v___x_1238_, v___x_1239_);
v___x_1241_ = lean_usize_land(v___x_1237_, v___x_1240_);
v_bucket_1242_ = lean_array_uget_borrowed(v_buckets_1228_, v___x_1241_);
v___x_1243_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_incrVar_spec__0_spec__0___redArg(v_a_1226_, v_bucket_1242_);
if (v___x_1243_ == 0)
{
lean_dec(v_a_1226_);
return v_m_1225_;
}
else
{
lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1254_; 
lean_inc(v_bucket_1242_);
lean_inc_ref(v_buckets_1228_);
lean_inc(v_size_1227_);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_m_1225_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; lean_object* v_unused_1256_; 
v_unused_1255_ = lean_ctor_get(v_m_1225_, 1);
lean_dec(v_unused_1255_);
v_unused_1256_ = lean_ctor_get(v_m_1225_, 0);
lean_dec(v_unused_1256_);
v___x_1245_ = v_m_1225_;
v_isShared_1246_ = v_isSharedCheck_1254_;
goto v_resetjp_1244_;
}
else
{
lean_dec(v_m_1225_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1254_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v_buckets_1248_; lean_object* v_bucket_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1247_ = lean_box(0);
v_buckets_1248_ = lean_array_uset(v_buckets_1228_, v___x_1241_, v___x_1247_);
v_bucket_1249_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0_spec__0(v_commonCnt_1224_, v_a_1226_, v_bucket_1242_);
v___x_1250_ = lean_array_uset(v_buckets_1248_, v___x_1241_, v_bucket_1249_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1250_);
v___x_1252_ = v___x_1245_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_size_1227_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0___boxed(lean_object* v_commonCnt_1257_, lean_object* v_m_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_commonCnt_1257_, v_m_1258_, v_a_1259_);
lean_dec(v_commonCnt_1257_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
return v_x_1261_;
}
else
{
lean_object* v_key_1263_; lean_object* v_value_1264_; lean_object* v_tail_1265_; lean_object* v___x_1266_; 
v_key_1263_ = lean_ctor_get(v_x_1262_, 0);
lean_inc(v_key_1263_);
v_value_1264_ = lean_ctor_get(v_x_1262_, 1);
lean_inc(v_value_1264_);
v_tail_1265_ = lean_ctor_get(v_x_1262_, 2);
lean_inc(v_tail_1265_);
lean_dec_ref_known(v_x_1262_, 3);
v___x_1266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1264_, v_x_1261_, v_key_1263_);
lean_dec(v_value_1264_);
v_x_1261_ = v___x_1266_;
v_x_1262_ = v_tail_1265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(lean_object* v_x_1268_, lean_object* v_x_1269_){
_start:
{
if (lean_obj_tag(v_x_1269_) == 0)
{
return v_x_1268_;
}
else
{
lean_object* v_key_1270_; lean_object* v_value_1271_; lean_object* v_tail_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_key_1270_ = lean_ctor_get(v_x_1269_, 0);
lean_inc(v_key_1270_);
v_value_1271_ = lean_ctor_get(v_x_1269_, 1);
lean_inc(v_value_1271_);
v_tail_1272_ = lean_ctor_get(v_x_1269_, 2);
lean_inc(v_tail_1272_);
lean_dec_ref_known(v_x_1269_, 3);
v___x_1273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__0(v_value_1271_, v_x_1268_, v_key_1270_);
lean_dec(v_value_1271_);
v___x_1274_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1_spec__2(v___x_1273_, v_tail_1272_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(lean_object* v_as_1275_, size_t v_i_1276_, size_t v_stop_1277_, lean_object* v_b_1278_){
_start:
{
uint8_t v___x_1279_; 
v___x_1279_ = lean_usize_dec_eq(v_i_1276_, v_stop_1277_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1281_; size_t v___x_1282_; size_t v___x_1283_; 
v___x_1280_ = lean_array_uget_borrowed(v_as_1275_, v_i_1276_);
lean_inc(v___x_1280_);
v___x_1281_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__1(v_b_1278_, v___x_1280_);
v___x_1282_ = ((size_t)1ULL);
v___x_1283_ = lean_usize_add(v_i_1276_, v___x_1282_);
v_i_1276_ = v___x_1283_;
v_b_1278_ = v___x_1281_;
goto _start;
}
else
{
return v_b_1278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2___boxed(lean_object* v_as_1285_, lean_object* v_i_1286_, lean_object* v_stop_1287_, lean_object* v_b_1288_){
_start:
{
size_t v_i_boxed_1289_; size_t v_stop_boxed_1290_; lean_object* v_res_1291_; 
v_i_boxed_1289_ = lean_unbox_usize(v_i_1286_);
lean_dec(v_i_1286_);
v_stop_boxed_1290_ = lean_unbox_usize(v_stop_1287_);
lean_dec(v_stop_1287_);
v_res_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_as_1285_, v_i_boxed_1289_, v_stop_boxed_1290_, v_b_1288_);
lean_dec_ref(v_as_1285_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(lean_object* v_x_1292_, lean_object* v_y_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v___y_1297_; lean_object* v_fst_1298_; lean_object* v_snd_1299_; lean_object* v_size_1303_; lean_object* v_buckets_1304_; lean_object* v_size_1305_; lean_object* v_buckets_1306_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1313_; lean_object* v_buckets_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v_buckets_1327_; lean_object* v_fst_1335_; lean_object* v_buckets_1336_; lean_object* v_snd_1337_; uint8_t v___x_1347_; 
v_size_1303_ = lean_ctor_get(v_y_1293_, 0);
lean_inc(v_size_1303_);
v_buckets_1304_ = lean_ctor_get(v_y_1293_, 1);
v_size_1305_ = lean_ctor_get(v_x_1292_, 0);
lean_inc(v_size_1305_);
v_buckets_1306_ = lean_ctor_get(v_x_1292_, 1);
v___x_1347_ = lean_nat_dec_lt(v_size_1303_, v_size_1305_);
if (v___x_1347_ == 0)
{
lean_inc_ref(v_buckets_1306_);
v_fst_1335_ = v_x_1292_;
v_buckets_1336_ = v_buckets_1306_;
v_snd_1337_ = v_y_1293_;
goto v___jp_1334_;
}
else
{
lean_inc_ref(v_buckets_1304_);
v_fst_1335_ = v_y_1293_;
v_buckets_1336_ = v_buckets_1304_;
v_snd_1337_ = v_x_1292_;
goto v___jp_1334_;
}
v___jp_1296_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1300_, 0, v___y_1297_);
lean_ctor_set(v___x_1300_, 1, v_fst_1298_);
lean_ctor_set(v___x_1300_, 2, v_snd_1299_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v_a_1294_);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
return v___x_1302_;
}
v___jp_1307_:
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_nat_dec_lt(v_size_1303_, v_size_1305_);
lean_dec(v_size_1305_);
lean_dec(v_size_1303_);
if (v___x_1311_ == 0)
{
v___y_1297_ = v___y_1309_;
v_fst_1298_ = v___y_1308_;
v_snd_1299_ = v___y_1310_;
goto v___jp_1296_;
}
else
{
v___y_1297_ = v___y_1309_;
v_fst_1298_ = v___y_1310_;
v_snd_1299_ = v___y_1308_;
goto v___jp_1296_;
}
}
v___jp_1312_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_array_get_size(v_buckets_1314_);
v___x_1319_ = lean_nat_dec_lt(v___x_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v_buckets_1314_);
v___y_1308_ = v___y_1316_;
v___y_1309_ = v___y_1313_;
v___y_1310_ = v___y_1315_;
goto v___jp_1307_;
}
else
{
size_t v___x_1320_; size_t v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = ((size_t)0ULL);
v___x_1321_ = lean_usize_of_nat(v___x_1318_);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1314_, v___x_1320_, v___x_1321_, v___y_1315_);
lean_dec_ref(v_buckets_1314_);
v___y_1308_ = v___y_1316_;
v___y_1309_ = v___y_1313_;
v___y_1310_ = v___x_1322_;
goto v___jp_1307_;
}
}
v___jp_1323_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = lean_array_get_size(v_buckets_1327_);
v___x_1330_ = lean_nat_dec_lt(v___x_1328_, v___x_1329_);
if (v___x_1330_ == 0)
{
v___y_1313_ = v___y_1326_;
v_buckets_1314_ = v_buckets_1327_;
v___y_1315_ = v___y_1325_;
v___y_1316_ = v___y_1324_;
goto v___jp_1312_;
}
else
{
size_t v___x_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = ((size_t)0ULL);
v___x_1332_ = lean_usize_of_nat(v___x_1329_);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__2(v_buckets_1327_, v___x_1331_, v___x_1332_, v___y_1324_);
v___y_1313_ = v___y_1326_;
v_buckets_1314_ = v_buckets_1327_;
v___y_1315_ = v___y_1325_;
v___y_1316_ = v___x_1333_;
goto v___jp_1312_;
}
}
v___jp_1334_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1338_ = lean_unsigned_to_nat(0u);
v___x_1339_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__0);
v___x_1340_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients___closed__1);
v___x_1341_ = lean_array_get_size(v_buckets_1336_);
v___x_1342_ = lean_nat_dec_lt(v___x_1338_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec_ref(v_buckets_1336_);
v___y_1324_ = v_fst_1335_;
v___y_1325_ = v_snd_1337_;
v___y_1326_ = v___x_1340_;
v_buckets_1327_ = v___x_1339_;
goto v___jp_1323_;
}
else
{
size_t v___x_1343_; size_t v___x_1344_; lean_object* v___x_1345_; lean_object* v_buckets_1346_; 
v___x_1343_ = ((size_t)0ULL);
v___x_1344_ = lean_usize_of_nat(v___x_1341_);
v___x_1345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__6(v_snd_1337_, v_buckets_1336_, v___x_1343_, v___x_1344_, v___x_1340_);
lean_dec_ref(v_buckets_1336_);
v_buckets_1346_ = lean_ctor_get(v___x_1345_, 1);
lean_inc_ref(v_buckets_1346_);
v___y_1324_ = v_fst_1335_;
v___y_1325_ = v_snd_1337_;
v___y_1326_ = v___x_1345_;
v_buckets_1327_ = v_buckets_1346_;
goto v___jp_1323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg___boxed(lean_object* v_x_1348_, lean_object* v_y_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1348_, v_y_1349_, v_a_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(lean_object* v_x_1353_, lean_object* v_y_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_x_1353_, v_y_1354_, v_a_1355_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___boxed(lean_object* v_x_1364_, lean_object* v_y_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute(v_x_1364_, v_y_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3(lean_object* v_00_u03b2_1375_, lean_object* v_m_1376_, lean_object* v_a_1377_, lean_object* v_b_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3___redArg(v_m_1376_, v_a_1377_, v_b_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(lean_object* v_00_u03b2_1380_, lean_object* v_m_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___redArg(v_m_1381_, v_a_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4___boxed(lean_object* v_00_u03b2_1384_, lean_object* v_m_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4(v_00_u03b2_1384_, v_m_1385_, v_a_1386_);
lean_dec(v_a_1386_);
lean_dec_ref(v_m_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5(lean_object* v_00_u03b2_1388_, lean_object* v_a_1389_, lean_object* v_b_1390_, lean_object* v_x_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__3_spec__5___redArg(v_a_1389_, v_b_1390_, v_x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(lean_object* v_00_u03b2_1393_, lean_object* v_a_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___redArg(v_a_1394_, v_x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1397_, lean_object* v_a_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute_spec__4_spec__7(v_00_u03b2_1397_, v_a_1398_, v_x_1399_);
lean_dec(v_x_1399_);
lean_dec(v_a_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(lean_object* v_x_1401_, lean_object* v_x_1402_){
_start:
{
if (lean_obj_tag(v_x_1402_) == 0)
{
return v_x_1401_;
}
else
{
lean_object* v_key_1403_; lean_object* v_value_1404_; lean_object* v_tail_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v_key_1403_ = lean_ctor_get(v_x_1402_, 0);
v_value_1404_ = lean_ctor_get(v_x_1402_, 1);
v_tail_1405_ = lean_ctor_get(v_x_1402_, 2);
lean_inc(v_value_1404_);
lean_inc(v_key_1403_);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_key_1403_);
lean_ctor_set(v___x_1406_, 1, v_value_1404_);
v___x_1407_ = lean_array_push(v_x_1401_, v___x_1406_);
v_x_1401_ = v___x_1407_;
v_x_1402_ = v_tail_1405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3___boxed(lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_x_1409_, v_x_1410_);
lean_dec(v_x_1410_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(lean_object* v_as_1412_, size_t v_i_1413_, size_t v_stop_1414_, lean_object* v_b_1415_){
_start:
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_usize_dec_eq(v_i_1413_, v_stop_1414_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; size_t v___x_1419_; size_t v___x_1420_; 
v___x_1417_ = lean_array_uget_borrowed(v_as_1412_, v_i_1413_);
v___x_1418_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__3(v_b_1415_, v___x_1417_);
v___x_1419_ = ((size_t)1ULL);
v___x_1420_ = lean_usize_add(v_i_1413_, v___x_1419_);
v_i_1413_ = v___x_1420_;
v_b_1415_ = v___x_1418_;
goto _start;
}
else
{
return v_b_1415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4___boxed(lean_object* v_as_1422_, lean_object* v_i_1423_, lean_object* v_stop_1424_, lean_object* v_b_1425_){
_start:
{
size_t v_i_boxed_1426_; size_t v_stop_boxed_1427_; lean_object* v_res_1428_; 
v_i_boxed_1426_ = lean_unbox_usize(v_i_1423_);
lean_dec(v_i_1423_);
v_stop_boxed_1427_ = lean_unbox_usize(v_stop_1424_);
lean_dec(v_stop_1424_);
v_res_1428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_as_1422_, v_i_boxed_1426_, v_stop_boxed_1427_, v_b_1425_);
lean_dec_ref(v_as_1422_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(lean_object* v_upperBound_1429_, lean_object* v___x_1430_, lean_object* v_op_1431_, lean_object* v_a_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___y_1437_; uint8_t v___x_1441_; 
v___x_1441_ = lean_nat_dec_lt(v_a_1432_, v_upperBound_1429_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_dec(v_a_1432_);
lean_dec_ref(v_op_1431_);
lean_dec_ref(v___x_1430_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v_b_1433_);
lean_ctor_set(v___x_1442_, 1, v___y_1434_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
else
{
if (lean_obj_tag(v_b_1433_) == 0)
{
lean_object* v___x_1444_; 
lean_inc_ref(v___x_1430_);
v___x_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1430_);
v___y_1437_ = v___x_1444_;
goto v___jp_1436_;
}
else
{
lean_object* v_val_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1454_; 
v_val_1445_ = lean_ctor_get(v_b_1433_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_b_1433_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1447_ = v_b_1433_;
v_isShared_1448_ = v_isSharedCheck_1454_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_val_1445_);
lean_dec(v_b_1433_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1454_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
lean_inc_ref(v_op_1431_);
v___x_1449_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_op_1431_);
lean_inc_ref(v___x_1430_);
v___x_1450_ = l_Lean_mkAppB(v___x_1449_, v_val_1445_, v___x_1430_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1450_);
v___x_1452_ = v___x_1447_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
v___y_1437_ = v___x_1452_;
goto v___jp_1436_;
}
}
}
}
v___jp_1436_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(1u);
v___x_1439_ = lean_nat_add(v_a_1432_, v___x_1438_);
lean_dec(v_a_1432_);
v_a_1432_ = v___x_1439_;
v_b_1433_ = v___y_1437_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg___boxed(lean_object* v_upperBound_1455_, lean_object* v___x_1456_, lean_object* v_op_1457_, lean_object* v_a_1458_, lean_object* v_b_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1455_, v___x_1456_, v_op_1457_, v_a_1458_, v_b_1459_, v___y_1460_);
lean_dec(v_upperBound_1455_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(lean_object* v_op_1463_, lean_object* v_as_1464_, size_t v_sz_1465_, size_t v_i_1466_, lean_object* v_b_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
uint8_t v___x_1476_; 
v___x_1476_ = lean_usize_dec_lt(v_i_1466_, v_sz_1465_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec_ref(v_op_1463_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_b_1467_);
lean_ctor_set(v___x_1477_, 1, v___y_1468_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
else
{
lean_object* v_a_1479_; lean_object* v_fst_1480_; lean_object* v_snd_1481_; lean_object* v_varToExpr_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v_a_1479_ = lean_array_uget_borrowed(v_as_1464_, v_i_1466_);
v_fst_1480_ = lean_ctor_get(v_a_1479_, 0);
v_snd_1481_ = lean_ctor_get(v_a_1479_, 1);
v_varToExpr_1482_ = lean_ctor_get(v___y_1468_, 2);
v___x_1483_ = l_Lean_instInhabitedExpr;
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = lean_array_get(v___x_1483_, v_varToExpr_1482_, v_fst_1480_);
lean_inc_ref(v_op_1463_);
v___x_1486_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_snd_1481_, v___x_1485_, v_op_1463_, v___x_1484_, v_b_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v_fst_1488_; lean_object* v_snd_1489_; size_t v___x_1490_; size_t v___x_1491_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v___x_1486_, 1);
v_fst_1488_ = lean_ctor_get(v_a_1487_, 0);
lean_inc(v_fst_1488_);
v_snd_1489_ = lean_ctor_get(v_a_1487_, 1);
lean_inc(v_snd_1489_);
lean_dec(v_a_1487_);
v___x_1490_ = ((size_t)1ULL);
v___x_1491_ = lean_usize_add(v_i_1466_, v___x_1490_);
v_i_1466_ = v___x_1491_;
v_b_1467_ = v_fst_1488_;
v___y_1468_ = v_snd_1489_;
goto _start;
}
else
{
lean_dec_ref(v_op_1463_);
return v___x_1486_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1___boxed(lean_object* v_op_1493_, lean_object* v_as_1494_, lean_object* v_sz_1495_, lean_object* v_i_1496_, lean_object* v_b_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
size_t v_sz_boxed_1506_; size_t v_i_boxed_1507_; lean_object* v_res_1508_; 
v_sz_boxed_1506_ = lean_unbox_usize(v_sz_1495_);
lean_dec(v_sz_1495_);
v_i_boxed_1507_ = lean_unbox_usize(v_i_1496_);
lean_dec(v_i_1496_);
v_res_1508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1493_, v_as_1494_, v_sz_boxed_1506_, v_i_boxed_1507_, v_b_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec_ref(v_as_1494_);
return v_res_1508_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(lean_object* v_x1_1509_, lean_object* v_x2_1510_){
_start:
{
lean_object* v_fst_1511_; lean_object* v_fst_1512_; uint8_t v___x_1513_; 
v_fst_1511_ = lean_ctor_get(v_x1_1509_, 0);
v_fst_1512_ = lean_ctor_get(v_x2_1510_, 0);
v___x_1513_ = lean_nat_dec_lt(v_fst_1511_, v_fst_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1514_, lean_object* v_x2_1515_){
_start:
{
uint8_t v_res_1516_; lean_object* v_r_1517_; 
v_res_1516_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v_x1_1514_, v_x2_1515_);
lean_dec_ref(v_x2_1515_);
lean_dec_ref(v_x1_1514_);
v_r_1517_ = lean_box(v_res_1516_);
return v_r_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(lean_object* v_hi_1518_, lean_object* v_pivot_1519_, lean_object* v_as_1520_, lean_object* v_i_1521_, lean_object* v_k_1522_){
_start:
{
uint8_t v___x_1523_; 
v___x_1523_ = lean_nat_dec_lt(v_k_1522_, v_hi_1518_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec(v_k_1522_);
v___x_1524_ = lean_array_fswap(v_as_1520_, v_i_1521_, v_hi_1518_);
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v_i_1521_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; lean_object* v_fst_1527_; lean_object* v_fst_1528_; uint8_t v___x_1529_; 
v___x_1526_ = lean_array_fget_borrowed(v_as_1520_, v_k_1522_);
v_fst_1527_ = lean_ctor_get(v___x_1526_, 0);
v_fst_1528_ = lean_ctor_get(v_pivot_1519_, 0);
v___x_1529_ = lean_nat_dec_lt(v_fst_1527_, v_fst_1528_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_unsigned_to_nat(1u);
v___x_1531_ = lean_nat_add(v_k_1522_, v___x_1530_);
lean_dec(v_k_1522_);
v_k_1522_ = v___x_1531_;
goto _start;
}
else
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1533_ = lean_array_fswap(v_as_1520_, v_i_1521_, v_k_1522_);
v___x_1534_ = lean_unsigned_to_nat(1u);
v___x_1535_ = lean_nat_add(v_i_1521_, v___x_1534_);
lean_dec(v_i_1521_);
v___x_1536_ = lean_nat_add(v_k_1522_, v___x_1534_);
lean_dec(v_k_1522_);
v_as_1520_ = v___x_1533_;
v_i_1521_ = v___x_1535_;
v_k_1522_ = v___x_1536_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg___boxed(lean_object* v_hi_1538_, lean_object* v_pivot_1539_, lean_object* v_as_1540_, lean_object* v_i_1541_, lean_object* v_k_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1538_, v_pivot_1539_, v_as_1540_, v_i_1541_, v_k_1542_);
lean_dec_ref(v_pivot_1539_);
lean_dec(v_hi_1538_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(lean_object* v_n_1544_, lean_object* v_as_1545_, lean_object* v_lo_1546_, lean_object* v_hi_1547_){
_start:
{
lean_object* v___y_1549_; uint8_t v___x_1559_; 
v___x_1559_ = lean_nat_dec_lt(v_lo_1546_, v_hi_1547_);
if (v___x_1559_ == 0)
{
lean_dec(v_lo_1546_);
return v_as_1545_;
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v_mid_1562_; lean_object* v___y_1564_; lean_object* v___y_1570_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1560_ = lean_nat_add(v_lo_1546_, v_hi_1547_);
v___x_1561_ = lean_unsigned_to_nat(1u);
v_mid_1562_ = lean_nat_shiftr(v___x_1560_, v___x_1561_);
lean_dec(v___x_1560_);
v___x_1575_ = lean_array_fget_borrowed(v_as_1545_, v_mid_1562_);
v___x_1576_ = lean_array_fget_borrowed(v_as_1545_, v_lo_1546_);
v___x_1577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1575_, v___x_1576_);
if (v___x_1577_ == 0)
{
v___y_1570_ = v_as_1545_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_array_fswap(v_as_1545_, v_lo_1546_, v_mid_1562_);
v___y_1570_ = v___x_1578_;
goto v___jp_1569_;
}
v___jp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1565_ = lean_array_fget_borrowed(v___y_1564_, v_mid_1562_);
v___x_1566_ = lean_array_fget_borrowed(v___y_1564_, v_hi_1547_);
v___x_1567_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1565_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_dec(v_mid_1562_);
v___y_1549_ = v___y_1564_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_array_fswap(v___y_1564_, v_mid_1562_, v_hi_1547_);
lean_dec(v_mid_1562_);
v___y_1549_ = v___x_1568_;
goto v___jp_1548_;
}
}
v___jp_1569_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1571_ = lean_array_fget_borrowed(v___y_1570_, v_hi_1547_);
v___x_1572_ = lean_array_fget_borrowed(v___y_1570_, v_lo_1546_);
v___x_1573_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___lam__0(v___x_1571_, v___x_1572_);
if (v___x_1573_ == 0)
{
v___y_1564_ = v___y_1570_;
goto v___jp_1563_;
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_array_fswap(v___y_1570_, v_lo_1546_, v_hi_1547_);
v___y_1564_ = v___x_1574_;
goto v___jp_1563_;
}
}
}
v___jp_1548_:
{
lean_object* v_pivot_1550_; lean_object* v___x_1551_; lean_object* v_fst_1552_; lean_object* v_snd_1553_; uint8_t v___x_1554_; 
v_pivot_1550_ = lean_array_fget(v___y_1549_, v_hi_1547_);
lean_inc_n(v_lo_1546_, 2);
v___x_1551_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1547_, v_pivot_1550_, v___y_1549_, v_lo_1546_, v_lo_1546_);
lean_dec(v_pivot_1550_);
v_fst_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_fst_1552_);
v_snd_1553_ = lean_ctor_get(v___x_1551_, 1);
lean_inc(v_snd_1553_);
lean_dec_ref(v___x_1551_);
v___x_1554_ = lean_nat_dec_le(v_hi_1547_, v_fst_1552_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1544_, v_snd_1553_, v_lo_1546_, v_fst_1552_);
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_add(v_fst_1552_, v___x_1556_);
lean_dec(v_fst_1552_);
v_as_1545_ = v___x_1555_;
v_lo_1546_ = v___x_1557_;
goto _start;
}
else
{
lean_dec(v_fst_1552_);
lean_dec(v_lo_1546_);
return v_snd_1553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg___boxed(lean_object* v_n_1579_, lean_object* v_as_1580_, lean_object* v_lo_1581_, lean_object* v_hi_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1579_, v_as_1580_, v_lo_1581_, v_hi_1582_);
lean_dec(v_hi_1582_);
lean_dec(v_n_1579_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(lean_object* v_coeff_1584_, lean_object* v_op_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v___y_1595_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1613_; lean_object* v_size_1620_; lean_object* v_buckets_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_size_1620_ = lean_ctor_get(v_coeff_1584_, 0);
v_buckets_1621_ = lean_ctor_get(v_coeff_1584_, 1);
v___x_1622_ = lean_mk_empty_array_with_capacity(v_size_1620_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_array_get_size(v_buckets_1621_);
v___x_1625_ = lean_nat_dec_lt(v___x_1623_, v___x_1624_);
if (v___x_1625_ == 0)
{
v___y_1613_ = v___x_1622_;
goto v___jp_1612_;
}
else
{
size_t v___x_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = ((size_t)0ULL);
v___x_1627_ = lean_usize_of_nat(v___x_1624_);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__4(v_buckets_1621_, v___x_1626_, v___x_1627_, v___x_1622_);
v___y_1613_ = v___x_1628_;
goto v___jp_1612_;
}
v___jp_1594_:
{
lean_object* v_acc_1596_; size_t v_sz_1597_; size_t v___x_1598_; lean_object* v___x_1599_; 
v_acc_1596_ = lean_box(0);
v_sz_1597_ = lean_array_size(v___y_1595_);
v___x_1598_ = ((size_t)0ULL);
v___x_1599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__1(v_op_1585_, v___y_1595_, v_sz_1597_, v___x_1598_, v_acc_1596_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
lean_dec_ref(v___y_1595_);
return v___x_1599_;
}
v___jp_1600_:
{
lean_object* v___x_1605_; 
v___x_1605_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v___y_1603_, v___y_1601_, v___y_1602_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec(v___y_1603_);
v___y_1595_ = v___x_1605_;
goto v___jp_1594_;
}
v___jp_1606_:
{
uint8_t v___x_1611_; 
v___x_1611_ = lean_nat_dec_le(v___y_1610_, v___y_1608_);
if (v___x_1611_ == 0)
{
lean_dec(v___y_1608_);
lean_inc(v___y_1610_);
v___y_1601_ = v___y_1607_;
v___y_1602_ = v___y_1610_;
v___y_1603_ = v___y_1609_;
v___y_1604_ = v___y_1610_;
goto v___jp_1600_;
}
else
{
v___y_1601_ = v___y_1607_;
v___y_1602_ = v___y_1610_;
v___y_1603_ = v___y_1609_;
v___y_1604_ = v___y_1608_;
goto v___jp_1600_;
}
}
v___jp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1614_ = lean_array_get_size(v___y_1613_);
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = lean_nat_dec_eq(v___x_1614_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1617_ = lean_unsigned_to_nat(1u);
v___x_1618_ = lean_nat_sub(v___x_1614_, v___x_1617_);
v___x_1619_ = lean_nat_dec_le(v___x_1615_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_inc(v___x_1618_);
v___y_1607_ = v___y_1613_;
v___y_1608_ = v___x_1618_;
v___y_1609_ = v___x_1614_;
v___y_1610_ = v___x_1618_;
goto v___jp_1606_;
}
else
{
v___y_1607_ = v___y_1613_;
v___y_1608_ = v___x_1618_;
v___y_1609_ = v___x_1614_;
v___y_1610_ = v___x_1615_;
goto v___jp_1606_;
}
}
else
{
v___y_1595_ = v___y_1613_;
goto v___jp_1594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr___boxed(lean_object* v_coeff_1629_, lean_object* v_op_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_coeff_1629_, v_op_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec_ref(v_coeff_1629_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(lean_object* v_upperBound_1640_, lean_object* v___x_1641_, lean_object* v_op_1642_, lean_object* v_inst_1643_, lean_object* v_R_1644_, lean_object* v_a_1645_, lean_object* v_b_1646_, lean_object* v_c_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___redArg(v_upperBound_1640_, v___x_1641_, v_op_1642_, v_a_1645_, v_b_1646_, v___y_1648_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0___boxed(lean_object* v_upperBound_1657_, lean_object* v___x_1658_, lean_object* v_op_1659_, lean_object* v_inst_1660_, lean_object* v_R_1661_, lean_object* v_a_1662_, lean_object* v_b_1663_, lean_object* v_c_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__0(v_upperBound_1657_, v___x_1658_, v_op_1659_, v_inst_1660_, v_R_1661_, v_a_1662_, v_b_1663_, v_c_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v_upperBound_1657_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(lean_object* v_n_1674_, lean_object* v_as_1675_, lean_object* v_lo_1676_, lean_object* v_hi_1677_, lean_object* v_w_1678_, lean_object* v_hlo_1679_, lean_object* v_hhi_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___redArg(v_n_1674_, v_as_1675_, v_lo_1676_, v_hi_1677_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2___boxed(lean_object* v_n_1682_, lean_object* v_as_1683_, lean_object* v_lo_1684_, lean_object* v_hi_1685_, lean_object* v_w_1686_, lean_object* v_hlo_1687_, lean_object* v_hhi_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2(v_n_1682_, v_as_1683_, v_lo_1684_, v_hi_1685_, v_w_1686_, v_hlo_1687_, v_hhi_1688_);
lean_dec(v_hi_1685_);
lean_dec(v_n_1682_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(lean_object* v_n_1690_, lean_object* v_lo_1691_, lean_object* v_hi_1692_, lean_object* v_hhi_1693_, lean_object* v_pivot_1694_, lean_object* v_as_1695_, lean_object* v_i_1696_, lean_object* v_k_1697_, lean_object* v_ilo_1698_, lean_object* v_ik_1699_, lean_object* v_w_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___redArg(v_hi_1692_, v_pivot_1694_, v_as_1695_, v_i_1696_, v_k_1697_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2___boxed(lean_object* v_n_1702_, lean_object* v_lo_1703_, lean_object* v_hi_1704_, lean_object* v_hhi_1705_, lean_object* v_pivot_1706_, lean_object* v_as_1707_, lean_object* v_i_1708_, lean_object* v_k_1709_, lean_object* v_ilo_1710_, lean_object* v_ik_1711_, lean_object* v_w_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr_spec__2_spec__2(v_n_1702_, v_lo_1703_, v_hi_1704_, v_hhi_1705_, v_pivot_1706_, v_as_1707_, v_i_1708_, v_k_1709_, v_ilo_1710_, v_ik_1711_, v_w_1712_);
lean_dec_ref(v_pivot_1706_);
lean_dec(v_hi_1704_);
lean_dec(v_lo_1703_);
lean_dec(v_n_1702_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(lean_object* v_e_1714_, lean_object* v___y_1715_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = l_Lean_Expr_hasMVar(v_e_1714_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_e_1714_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; lean_object* v_mctx_1720_; lean_object* v___x_1721_; lean_object* v_fst_1722_; lean_object* v_snd_1723_; lean_object* v___x_1724_; lean_object* v_cache_1725_; lean_object* v_zetaDeltaFVarIds_1726_; lean_object* v_postponed_1727_; lean_object* v_diag_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1737_; 
v___x_1719_ = lean_st_ref_get(v___y_1715_);
v_mctx_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc_ref(v_mctx_1720_);
lean_dec(v___x_1719_);
v___x_1721_ = l_Lean_instantiateMVarsCore(v_mctx_1720_, v_e_1714_);
v_fst_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_fst_1722_);
v_snd_1723_ = lean_ctor_get(v___x_1721_, 1);
lean_inc(v_snd_1723_);
lean_dec_ref(v___x_1721_);
v___x_1724_ = lean_st_ref_take(v___y_1715_);
v_cache_1725_ = lean_ctor_get(v___x_1724_, 1);
v_zetaDeltaFVarIds_1726_ = lean_ctor_get(v___x_1724_, 2);
v_postponed_1727_ = lean_ctor_get(v___x_1724_, 3);
v_diag_1728_ = lean_ctor_get(v___x_1724_, 4);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; 
v_unused_1738_ = lean_ctor_get(v___x_1724_, 0);
lean_dec(v_unused_1738_);
v___x_1730_ = v___x_1724_;
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_diag_1728_);
lean_inc(v_postponed_1727_);
lean_inc(v_zetaDeltaFVarIds_1726_);
lean_inc(v_cache_1725_);
lean_dec(v___x_1724_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v_snd_1723_);
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_snd_1723_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_cache_1725_);
lean_ctor_set(v_reuseFailAlloc_1736_, 2, v_zetaDeltaFVarIds_1726_);
lean_ctor_set(v_reuseFailAlloc_1736_, 3, v_postponed_1727_);
lean_ctor_set(v_reuseFailAlloc_1736_, 4, v_diag_1728_);
v___x_1733_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_st_ref_put(v___y_1715_, v___x_1733_);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_fst_1722_);
return v___x_1735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg___boxed(lean_object* v_e_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1739_, v___y_1740_);
lean_dec(v___y_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(lean_object* v_e_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_e_1743_, v___y_1745_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___boxed(lean_object* v_e_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0(v_e_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(lean_object* v_x_1757_, lean_object* v_y_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Meta_mkEq(v_x_1757_, v_y_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1787_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1787_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1787_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 1);
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
uint8_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = 0;
v___x_1772_ = lean_box(0);
v___x_1773_ = l_Lean_Meta_mkFreshExprMVar(v___x_1770_, v___x_1771_, v___x_1772_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v___x_1775_ = l_Lean_Expr_mvarId_x21(v_a_1774_);
v___x_1776_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(v___x_1775_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v___x_1777_; 
lean_dec_ref_known(v___x_1776_, 1);
v___x_1777_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC_spec__0___redArg(v_a_1774_, v_a_1760_);
return v___x_1777_;
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v_a_1774_);
v_a_1778_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1776_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1776_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
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
}
else
{
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC___boxed(lean_object* v_x_1788_, lean_object* v_y_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v_x_1788_, v_y_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
return v_res_1795_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = lean_unsigned_to_nat(32u);
v___x_1797_ = lean_mk_empty_array_with_capacity(v___x_1796_);
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1799_ = ((size_t)5ULL);
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = lean_unsigned_to_nat(32u);
v___x_1802_ = lean_mk_empty_array_with_capacity(v___x_1801_);
v___x_1803_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__0);
v___x_1804_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
lean_ctor_set(v___x_1804_, 1, v___x_1802_);
lean_ctor_set(v___x_1804_, 2, v___x_1800_);
lean_ctor_set(v___x_1804_, 3, v___x_1800_);
lean_ctor_set_usize(v___x_1804_, 4, v___x_1799_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; lean_object* v_traceState_1808_; lean_object* v_traces_1809_; lean_object* v___x_1810_; lean_object* v_traceState_1811_; lean_object* v_env_1812_; lean_object* v_nextMacroScope_1813_; lean_object* v_ngen_1814_; lean_object* v_auxDeclNGen_1815_; lean_object* v_cache_1816_; lean_object* v_recordedDeps_1817_; lean_object* v_messages_1818_; lean_object* v_infoState_1819_; lean_object* v_snapshotTasks_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1839_; 
v___x_1807_ = lean_st_ref_get(v___y_1805_);
v_traceState_1808_ = lean_ctor_get(v___x_1807_, 4);
lean_inc_ref(v_traceState_1808_);
lean_dec(v___x_1807_);
v_traces_1809_ = lean_ctor_get(v_traceState_1808_, 0);
lean_inc_ref(v_traces_1809_);
lean_dec_ref(v_traceState_1808_);
v___x_1810_ = lean_st_ref_take(v___y_1805_);
v_traceState_1811_ = lean_ctor_get(v___x_1810_, 4);
v_env_1812_ = lean_ctor_get(v___x_1810_, 0);
v_nextMacroScope_1813_ = lean_ctor_get(v___x_1810_, 1);
v_ngen_1814_ = lean_ctor_get(v___x_1810_, 2);
v_auxDeclNGen_1815_ = lean_ctor_get(v___x_1810_, 3);
v_cache_1816_ = lean_ctor_get(v___x_1810_, 5);
v_recordedDeps_1817_ = lean_ctor_get(v___x_1810_, 6);
v_messages_1818_ = lean_ctor_get(v___x_1810_, 7);
v_infoState_1819_ = lean_ctor_get(v___x_1810_, 8);
v_snapshotTasks_1820_ = lean_ctor_get(v___x_1810_, 9);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1822_ = v___x_1810_;
v_isShared_1823_ = v_isSharedCheck_1839_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_snapshotTasks_1820_);
lean_inc(v_infoState_1819_);
lean_inc(v_messages_1818_);
lean_inc(v_recordedDeps_1817_);
lean_inc(v_cache_1816_);
lean_inc(v_traceState_1811_);
lean_inc(v_auxDeclNGen_1815_);
lean_inc(v_ngen_1814_);
lean_inc(v_nextMacroScope_1813_);
lean_inc(v_env_1812_);
lean_dec(v___x_1810_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1839_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
uint64_t v_tid_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1837_; 
v_tid_1824_ = lean_ctor_get_uint64(v_traceState_1811_, sizeof(void*)*1);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_traceState_1811_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; 
v_unused_1838_ = lean_ctor_get(v_traceState_1811_, 0);
lean_dec(v_unused_1838_);
v___x_1826_ = v_traceState_1811_;
v_isShared_1827_ = v_isSharedCheck_1837_;
goto v_resetjp_1825_;
}
else
{
lean_dec(v_traceState_1811_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1837_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___closed__1);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1828_);
v___x_1830_ = v___x_1826_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1828_);
lean_ctor_set_uint64(v_reuseFailAlloc_1836_, sizeof(void*)*1, v_tid_1824_);
v___x_1830_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1832_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 4, v___x_1830_);
v___x_1832_ = v___x_1822_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_env_1812_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_nextMacroScope_1813_);
lean_ctor_set(v_reuseFailAlloc_1835_, 2, v_ngen_1814_);
lean_ctor_set(v_reuseFailAlloc_1835_, 3, v_auxDeclNGen_1815_);
lean_ctor_set(v_reuseFailAlloc_1835_, 4, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1835_, 5, v_cache_1816_);
lean_ctor_set(v_reuseFailAlloc_1835_, 6, v_recordedDeps_1817_);
lean_ctor_set(v_reuseFailAlloc_1835_, 7, v_messages_1818_);
lean_ctor_set(v_reuseFailAlloc_1835_, 8, v_infoState_1819_);
lean_ctor_set(v_reuseFailAlloc_1835_, 9, v_snapshotTasks_1820_);
v___x_1832_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_st_ref_put(v___y_1805_, v___x_1832_);
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v_traces_1809_);
return v___x_1834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg___boxed(lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1840_);
lean_dec(v___y_1840_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v___y_1851_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___boxed(lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1(v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
return v_res_1864_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(lean_object* v_opts_1865_, lean_object* v_opt_1866_){
_start:
{
lean_object* v_name_1867_; lean_object* v_defValue_1868_; lean_object* v_map_1869_; lean_object* v___x_1870_; 
v_name_1867_ = lean_ctor_get(v_opt_1866_, 0);
v_defValue_1868_ = lean_ctor_get(v_opt_1866_, 1);
v_map_1869_ = lean_ctor_get(v_opts_1865_, 0);
v___x_1870_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1869_, v_name_1867_);
if (lean_obj_tag(v___x_1870_) == 0)
{
uint8_t v___x_1871_; 
v___x_1871_ = lean_unbox(v_defValue_1868_);
return v___x_1871_;
}
else
{
lean_object* v_val_1872_; 
v_val_1872_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_val_1872_);
lean_dec_ref_known(v___x_1870_, 1);
if (lean_obj_tag(v_val_1872_) == 1)
{
uint8_t v_v_1873_; 
v_v_1873_ = lean_ctor_get_uint8(v_val_1872_, 0);
lean_dec_ref_known(v_val_1872_, 0);
return v_v_1873_;
}
else
{
uint8_t v___x_1874_; 
lean_dec(v_val_1872_);
v___x_1874_ = lean_unbox(v_defValue_1868_);
return v___x_1874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2___boxed(lean_object* v_opts_1875_, lean_object* v_opt_1876_){
_start:
{
uint8_t v_res_1877_; lean_object* v_r_1878_; 
v_res_1877_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_1875_, v_opt_1876_);
lean_dec_ref(v_opt_1876_);
lean_dec_ref(v_opts_1875_);
v_r_1878_ = lean_box(v_res_1877_);
return v_r_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(lean_object* v_cls_1879_, lean_object* v_____do__lift_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_toCold_1891_; lean_object* v_options_1892_; uint8_t v_hasTrace_1893_; 
v_toCold_1891_ = lean_ctor_get(v___y_1888_, 0);
v_options_1892_ = lean_ctor_get(v_toCold_1891_, 2);
v_hasTrace_1893_ = lean_ctor_get_uint8(v_options_1892_, sizeof(void*)*1);
if (v_hasTrace_1893_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec(v_cls_1879_);
v___x_1894_ = lean_box(v_hasTrace_1893_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1896_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
v___x_1897_ = l_Lean_Name_append(v___x_1896_, v_cls_1879_);
v___x_1898_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_1880_, v_options_1892_, v___x_1897_);
lean_dec(v___x_1897_);
v___x_1899_ = lean_box(v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0___boxed(lean_object* v_cls_1901_, lean_object* v_____do__lift_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_1901_, v_____do__lift_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v_____do__lift_1902_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1(lean_object* v___x_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_mkAppB(v___x_1914_, v___y_1915_, v___y_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(lean_object* v_val_1918_, lean_object* v_lhs_1919_, lean_object* v_rhs_1920_, lean_object* v_P_1921_, uint8_t v___x_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; 
lean_inc_ref(v_lhs_1919_);
lean_inc_ref(v_val_1918_);
v___x_1931_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1918_, v_lhs_1919_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v_fst_1933_; lean_object* v_snd_1934_; lean_object* v___x_1935_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v_fst_1933_ = lean_ctor_get(v_a_1932_, 0);
lean_inc(v_fst_1933_);
v_snd_1934_ = lean_ctor_get(v_a_1932_, 1);
lean_inc(v_snd_1934_);
lean_dec(v_a_1932_);
lean_inc_ref(v_rhs_1920_);
lean_inc_ref(v_val_1918_);
v___x_1935_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients(v_val_1918_, v_rhs_1920_, v_snd_1934_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v_fst_1937_; lean_object* v_snd_1938_; lean_object* v___x_1939_; lean_object* v_a_1940_; lean_object* v_fst_1941_; lean_object* v_snd_1942_; lean_object* v_common_1943_; lean_object* v_x_1944_; lean_object* v_y_1945_; lean_object* v___x_1946_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v_fst_1937_ = lean_ctor_get(v_a_1936_, 0);
lean_inc(v_fst_1937_);
v_snd_1938_ = lean_ctor_get(v_a_1936_, 1);
lean_inc(v_snd_1938_);
lean_dec(v_a_1936_);
v___x_1939_ = l_Lean_Meta_Tactic_BVDecide_Normalize_SharedCoefficients_compute___redArg(v_fst_1933_, v_fst_1937_, v_snd_1938_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref(v___x_1939_);
v_fst_1941_ = lean_ctor_get(v_a_1940_, 0);
lean_inc(v_fst_1941_);
v_snd_1942_ = lean_ctor_get(v_a_1940_, 1);
lean_inc(v_snd_1942_);
lean_dec(v_a_1940_);
v_common_1943_ = lean_ctor_get(v_fst_1941_, 0);
lean_inc_ref(v_common_1943_);
v_x_1944_ = lean_ctor_get(v_fst_1941_, 1);
lean_inc_ref(v_x_1944_);
v_y_1945_ = lean_ctor_get(v_fst_1941_, 2);
lean_inc_ref(v_y_1945_);
lean_dec(v_fst_1941_);
lean_inc_ref(v_val_1918_);
v___x_1946_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_common_1943_, v_val_1918_, v_snd_1942_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec_ref(v_common_1943_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v_fst_1948_; lean_object* v_snd_1949_; lean_object* v___x_1950_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v_fst_1948_ = lean_ctor_get(v_a_1947_, 0);
lean_inc(v_fst_1948_);
v_snd_1949_ = lean_ctor_get(v_a_1947_, 1);
lean_inc(v_snd_1949_);
lean_dec(v_a_1947_);
lean_inc_ref(v_val_1918_);
v___x_1950_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_x_1944_, v_val_1918_, v_snd_1949_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec_ref(v_x_1944_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v_fst_1952_; lean_object* v_snd_1953_; lean_object* v___x_1954_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v_fst_1952_ = lean_ctor_get(v_a_1951_, 0);
lean_inc(v_fst_1952_);
v_snd_1953_ = lean_ctor_get(v_a_1951_, 1);
lean_inc(v_snd_1953_);
lean_dec(v_a_1951_);
lean_inc_ref(v_val_1918_);
v___x_1954_ = l_Lean_Meta_Tactic_BVDecide_Normalize_CoefficientsMap_toExpr(v_y_1945_, v_val_1918_, v_snd_1953_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec_ref(v_y_1945_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_2019_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_2019_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_2019_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v_fst_1959_; lean_object* v_snd_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_2018_; 
v_fst_1959_ = lean_ctor_get(v_a_1955_, 0);
v_snd_1960_ = lean_ctor_get(v_a_1955_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_a_1955_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1962_ = v_a_1955_;
v_isShared_1963_ = v_isSharedCheck_2018_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_snd_1960_);
lean_inc(v_fst_1959_);
lean_dec(v_a_1955_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_2018_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___x_2008_; lean_object* v___f_2009_; lean_object* v___y_2011_; lean_object* v___x_2015_; 
lean_inc_ref(v_val_1918_);
v___x_2008_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_1918_);
v___f_2009_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__1), 3, 1);
lean_closure_set(v___f_2009_, 0, v___x_2008_);
lean_inc(v_fst_1948_);
lean_inc_ref(v___f_2009_);
v___x_2015_ = l_Option_merge___redArg(v___f_2009_, v_fst_1948_, v_fst_1952_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2016_; 
lean_inc_ref(v_val_1918_);
v___x_2016_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1918_);
v___y_2011_ = v___x_2016_;
goto v___jp_2010_;
}
else
{
lean_object* v_val_2017_; 
v_val_2017_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_val_2017_);
lean_dec_ref_known(v___x_2015_, 1);
v___y_2011_ = v_val_2017_;
goto v___jp_2010_;
}
v___jp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
lean_inc_ref(v_P_1921_);
v___x_1967_ = l_Lean_mkAppB(v_P_1921_, v_lhs_1919_, v_rhs_1920_);
v___x_1968_ = l_Lean_mkAppB(v_P_1921_, v___y_1965_, v___y_1966_);
v___x_1969_ = lean_expr_eqv(v___x_1967_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_del_object(v___x_1957_);
lean_inc_ref(v___x_1968_);
v___x_1970_ = l_Lean_Meta_Tactic_BVDecide_Normalize_proveEqualityByAC(v___x_1967_, v___x_1968_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1972_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
v___x_1972_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1968_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1984_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1984_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1984_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1977_, 0, v_a_1973_);
lean_ctor_set(v___x_1977_, 1, v_a_1971_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*2, v___x_1969_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*2 + 1, v___x_1969_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1977_);
v___x_1979_ = v___x_1962_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_snd_1960_);
v___x_1979_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1979_);
v___x_1981_ = v___x_1975_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec(v_a_1971_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
v_a_1985_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1972_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1972_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v___x_1968_);
lean_del_object(v___x_1962_);
lean_dec(v_snd_1960_);
v_a_1993_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1970_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1970_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2003_; 
lean_dec_ref(v___x_1968_);
lean_dec_ref(v___x_1967_);
v___x_2001_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2001_, 0, v___x_1922_);
lean_ctor_set_uint8(v___x_2001_, 1, v___x_1922_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_2001_);
v___x_2003_ = v___x_1962_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_snd_1960_);
v___x_2003_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
lean_object* v___x_2005_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_2003_);
v___x_2005_ = v___x_1957_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
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
v___jp_2010_:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Option_merge___redArg(v___f_2009_, v_fst_1948_, v_fst_1959_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_neutralElement(v_val_1918_);
v___y_1965_ = v___y_2011_;
v___y_1966_ = v___x_2013_;
goto v___jp_1964_;
}
else
{
lean_object* v_val_2014_; 
lean_dec_ref(v_val_1918_);
v_val_2014_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_val_2014_);
lean_dec_ref_known(v___x_2012_, 1);
v___y_1965_ = v___y_2011_;
v___y_1966_ = v_val_2014_;
goto v___jp_1964_;
}
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_fst_1952_);
lean_dec(v_fst_1948_);
lean_dec_ref(v_P_1921_);
lean_dec_ref(v_rhs_1920_);
lean_dec_ref(v_lhs_1919_);
lean_dec_ref(v_val_1918_);
v_a_2020_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1954_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1954_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_fst_1948_);
lean_dec_ref(v_y_1945_);
lean_dec_ref(v_P_1921_);
lean_dec_ref(v_rhs_1920_);
lean_dec_ref(v_lhs_1919_);
lean_dec_ref(v_val_1918_);
v_a_2028_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_1950_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_1950_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec_ref(v_y_1945_);
lean_dec_ref(v_x_1944_);
lean_dec_ref(v_P_1921_);
lean_dec_ref(v_rhs_1920_);
lean_dec_ref(v_lhs_1919_);
lean_dec_ref(v_val_1918_);
v_a_2036_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_1946_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_1946_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v_fst_1933_);
lean_dec_ref(v_P_1921_);
lean_dec_ref(v_rhs_1920_);
lean_dec_ref(v_lhs_1919_);
lean_dec_ref(v_val_1918_);
v_a_2044_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_1935_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_1935_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
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
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v_P_1921_);
lean_dec_ref(v_rhs_1920_);
lean_dec_ref(v_lhs_1919_);
lean_dec_ref(v_val_1918_);
v_a_2052_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_1931_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_1931_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed(lean_object* v_val_2060_, lean_object* v_lhs_2061_, lean_object* v_rhs_2062_, lean_object* v_P_2063_, lean_object* v___x_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
uint8_t v___x_187981__boxed_2073_; lean_object* v_res_2074_; 
v___x_187981__boxed_2073_ = lean_unbox(v___x_2064_);
v_res_2074_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2(v_val_2060_, v_lhs_2061_, v_rhs_2062_, v_P_2063_, v___x_187981__boxed_2073_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
return v_res_2074_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__0));
v___x_2077_ = l_Lean_stringToMessageData(v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(lean_object* v_x_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___closed__1);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3___boxed(lean_object* v_x_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__3(v_x_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v_x_2091_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(lean_object* v_cls_2103_, lean_object* v_msg_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_ref_2110_; lean_object* v___x_2111_; lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2157_; 
v_ref_2110_ = lean_ctor_get(v___y_2107_, 2);
v___x_2111_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2157_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2157_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v_traceState_2117_; lean_object* v_env_2118_; lean_object* v_nextMacroScope_2119_; lean_object* v_ngen_2120_; lean_object* v_auxDeclNGen_2121_; lean_object* v_cache_2122_; lean_object* v_recordedDeps_2123_; lean_object* v_messages_2124_; lean_object* v_infoState_2125_; lean_object* v_snapshotTasks_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2156_; 
v___x_2116_ = lean_st_ref_take(v___y_2108_);
v_traceState_2117_ = lean_ctor_get(v___x_2116_, 4);
v_env_2118_ = lean_ctor_get(v___x_2116_, 0);
v_nextMacroScope_2119_ = lean_ctor_get(v___x_2116_, 1);
v_ngen_2120_ = lean_ctor_get(v___x_2116_, 2);
v_auxDeclNGen_2121_ = lean_ctor_get(v___x_2116_, 3);
v_cache_2122_ = lean_ctor_get(v___x_2116_, 5);
v_recordedDeps_2123_ = lean_ctor_get(v___x_2116_, 6);
v_messages_2124_ = lean_ctor_get(v___x_2116_, 7);
v_infoState_2125_ = lean_ctor_get(v___x_2116_, 8);
v_snapshotTasks_2126_ = lean_ctor_get(v___x_2116_, 9);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2128_ = v___x_2116_;
v_isShared_2129_ = v_isSharedCheck_2156_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_snapshotTasks_2126_);
lean_inc(v_infoState_2125_);
lean_inc(v_messages_2124_);
lean_inc(v_recordedDeps_2123_);
lean_inc(v_cache_2122_);
lean_inc(v_traceState_2117_);
lean_inc(v_auxDeclNGen_2121_);
lean_inc(v_ngen_2120_);
lean_inc(v_nextMacroScope_2119_);
lean_inc(v_env_2118_);
lean_dec(v___x_2116_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2156_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
uint64_t v_tid_2130_; lean_object* v_traces_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2155_; 
v_tid_2130_ = lean_ctor_get_uint64(v_traceState_2117_, sizeof(void*)*1);
v_traces_2131_ = lean_ctor_get(v_traceState_2117_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_traceState_2117_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2133_ = v_traceState_2117_;
v_isShared_2134_ = v_isSharedCheck_2155_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_traces_2131_);
lean_dec(v_traceState_2117_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2155_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; double v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2135_ = lean_box(0);
v___x_2136_ = lean_box(0);
v___x_2137_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_2138_ = 0;
v___x_2139_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_2140_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2140_, 0, v_cls_2103_);
lean_ctor_set(v___x_2140_, 1, v___x_2136_);
lean_ctor_set(v___x_2140_, 2, v___x_2139_);
lean_ctor_set_float(v___x_2140_, sizeof(void*)*3, v___x_2137_);
lean_ctor_set_float(v___x_2140_, sizeof(void*)*3 + 8, v___x_2137_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*3 + 16, v___x_2138_);
v___x_2141_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_2142_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2140_);
lean_ctor_set(v___x_2142_, 1, v_a_2112_);
lean_ctor_set(v___x_2142_, 2, v___x_2141_);
lean_inc(v_ref_2110_);
v___x_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2143_, 0, v_ref_2110_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_PersistentArray_push___redArg(v_traces_2131_, v___x_2143_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2144_);
v___x_2146_ = v___x_2133_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2144_);
lean_ctor_set_uint64(v_reuseFailAlloc_2154_, sizeof(void*)*1, v_tid_2130_);
v___x_2146_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2148_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 4, v___x_2146_);
v___x_2148_ = v___x_2128_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_env_2118_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_nextMacroScope_2119_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_ngen_2120_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v_auxDeclNGen_2121_);
lean_ctor_set(v_reuseFailAlloc_2153_, 4, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2153_, 5, v_cache_2122_);
lean_ctor_set(v_reuseFailAlloc_2153_, 6, v_recordedDeps_2123_);
lean_ctor_set(v_reuseFailAlloc_2153_, 7, v_messages_2124_);
lean_ctor_set(v_reuseFailAlloc_2153_, 8, v_infoState_2125_);
lean_ctor_set(v_reuseFailAlloc_2153_, 9, v_snapshotTasks_2126_);
v___x_2148_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = lean_st_ref_put(v___y_2108_, v___x_2148_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2135_);
v___x_2151_ = v___x_2114_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2135_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg___boxed(lean_object* v_cls_2158_, lean_object* v_msg_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2158_, v_msg_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
return v_res_2165_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__1));
v___x_2170_ = l_Lean_stringToMessageData(v___x_2169_);
return v___x_2170_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__3));
v___x_2173_ = l_Lean_stringToMessageData(v___x_2172_);
return v___x_2173_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__5));
v___x_2176_ = l_Lean_stringToMessageData(v___x_2175_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = lean_box(0);
v___x_2178_ = lean_unsigned_to_nat(16u);
v___x_2179_ = lean_mk_array(v___x_2178_, v___x_2177_);
return v___x_2179_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__7);
v___x_2181_ = lean_unsigned_to_nat(0u);
v___x_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2180_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__10));
v___x_2187_ = l_Lean_stringToMessageData(v___x_2186_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__12));
v___x_2190_ = l_Lean_stringToMessageData(v___x_2189_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__14));
v___x_2193_ = l_Lean_stringToMessageData(v___x_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(lean_object* v_lhs_2194_, lean_object* v_rhs_2195_, lean_object* v___f_2196_, lean_object* v_cls_2197_, lean_object* v_P_2198_, lean_object* v_____r_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2194_);
if (lean_obj_tag(v___x_2216_) == 1)
{
lean_object* v_val_2217_; lean_object* v___x_2218_; 
v_val_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v___x_2218_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2195_);
if (lean_obj_tag(v___x_2218_) == 1)
{
lean_object* v_val_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2303_; 
v_val_2219_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2221_ = v___x_2218_;
v_isShared_2222_ = v_isSharedCheck_2303_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_val_2219_);
lean_dec(v___x_2218_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2303_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
uint8_t v___x_2223_; 
v___x_2223_ = lean_expr_eqv(v_val_2217_, v_val_2219_);
if (v___x_2223_ == 0)
{
lean_object* v_toCold_2229_; lean_object* v_inheritedTraceOptions_2230_; lean_object* v___x_2231_; 
lean_dec_ref(v_P_2198_);
v_toCold_2229_ = lean_ctor_get(v___y_2207_, 0);
v_inheritedTraceOptions_2230_ = lean_ctor_get(v_toCold_2229_, 11);
lean_inc(v___y_2208_);
lean_inc_ref(v___y_2207_);
lean_inc(v___y_2206_);
lean_inc_ref(v___y_2205_);
lean_inc(v___y_2204_);
lean_inc_ref(v___y_2203_);
lean_inc(v___y_2202_);
lean_inc_ref(v___y_2201_);
lean_inc(v___y_2200_);
lean_inc_ref(v_inheritedTraceOptions_2230_);
v___x_2231_ = lean_apply_11(v___f_2196_, v_inheritedTraceOptions_2230_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, lean_box(0));
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; uint8_t v___x_2233_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2231_, 1);
v___x_2233_ = lean_unbox(v_a_2232_);
lean_dec(v_a_2232_);
if (v___x_2233_ == 0)
{
lean_dec(v_val_2219_);
lean_dec(v_val_2217_);
lean_dec(v_cls_2197_);
lean_dec_ref(v_rhs_2195_);
lean_dec_ref(v_lhs_2194_);
goto v___jp_2224_;
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2234_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2);
v___x_2235_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2217_);
v___x_2236_ = l_Lean_MessageData_ofExpr(v___x_2235_);
v___x_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2234_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2237_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = l_Lean_indentExpr(v_lhs_2194_);
v___x_2241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2239_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6);
v___x_2243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2219_);
v___x_2245_ = l_Lean_MessageData_ofExpr(v___x_2244_);
v___x_2246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2243_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set(v___x_2247_, 1, v___x_2238_);
v___x_2248_ = l_Lean_indentExpr(v_rhs_2195_);
v___x_2249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2197_, v___x_2249_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_dec_ref_known(v___x_2250_, 1);
goto v___jp_2224_;
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_del_object(v___x_2221_);
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_del_object(v___x_2221_);
lean_dec(v_val_2219_);
lean_dec(v_val_2217_);
lean_dec(v_cls_2197_);
lean_dec_ref(v_rhs_2195_);
lean_dec_ref(v_lhs_2194_);
v_a_2259_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2231_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2231_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v_toCold_2267_; lean_object* v_options_2268_; lean_object* v_inheritedTraceOptions_2269_; uint8_t v_hasTrace_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___f_2273_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; 
lean_del_object(v___x_2221_);
lean_dec(v_val_2219_);
lean_dec_ref(v___f_2196_);
v_toCold_2267_ = lean_ctor_get(v___y_2207_, 0);
v_options_2268_ = lean_ctor_get(v_toCold_2267_, 2);
v_inheritedTraceOptions_2269_ = lean_ctor_get(v_toCold_2267_, 11);
v_hasTrace_2270_ = lean_ctor_get_uint8(v_options_2268_, sizeof(void*)*1);
v___x_2271_ = 0;
v___x_2272_ = lean_box(v___x_2271_);
lean_inc(v_val_2217_);
v___f_2273_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_2273_, 0, v_val_2217_);
lean_closure_set(v___f_2273_, 1, v_lhs_2194_);
lean_closure_set(v___f_2273_, 2, v_rhs_2195_);
lean_closure_set(v___f_2273_, 3, v_P_2198_);
lean_closure_set(v___f_2273_, 4, v___x_2272_);
if (v_hasTrace_2270_ == 0)
{
lean_dec(v_cls_2197_);
v___y_2275_ = v___y_2203_;
v___y_2276_ = v___y_2204_;
v___y_2277_ = v___y_2205_;
v___y_2278_ = v___y_2206_;
v___y_2279_ = v___y_2207_;
v___y_2280_ = v___y_2208_;
goto v___jp_2274_;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2197_);
v___x_2286_ = l_Lean_Name_append(v___x_2285_, v_cls_2197_);
v___x_2287_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2269_, v_options_2268_, v___x_2286_);
lean_dec(v___x_2286_);
if (v___x_2287_ == 0)
{
lean_dec(v_cls_2197_);
v___y_2275_ = v___y_2203_;
v___y_2276_ = v___y_2204_;
v___y_2277_ = v___y_2205_;
v___y_2278_ = v___y_2206_;
v___y_2279_ = v___y_2207_;
v___y_2280_ = v___y_2208_;
goto v___jp_2274_;
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2288_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11);
lean_inc(v_val_2217_);
v___x_2289_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2217_);
v___x_2290_ = l_Lean_MessageData_ofExpr(v___x_2289_);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2288_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2197_, v___x_2293_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_dec_ref_known(v___x_2294_, 1);
v___y_2275_ = v___y_2203_;
v___y_2276_ = v___y_2204_;
v___y_2277_ = v___y_2205_;
v___y_2278_ = v___y_2206_;
v___y_2279_ = v___y_2207_;
v___y_2280_ = v___y_2208_;
goto v___jp_2274_;
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec_ref(v___f_2273_);
lean_dec(v_val_2217_);
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
v___jp_2274_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2281_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8);
v___x_2282_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9));
v___x_2283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2283_, 0, v_val_2217_);
lean_ctor_set(v___x_2283_, 1, v___x_2281_);
lean_ctor_set(v___x_2283_, 2, v___x_2282_);
v___x_2284_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2273_, v___x_2283_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
return v___x_2284_;
}
}
v___jp_2224_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2225_, 0, v___x_2223_);
lean_ctor_set_uint8(v___x_2225_, 1, v___x_2223_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set_tag(v___x_2221_, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2225_);
v___x_2227_ = v___x_2221_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v_toCold_2304_; lean_object* v_inheritedTraceOptions_2305_; lean_object* v___x_2306_; 
lean_dec(v___x_2218_);
lean_dec(v_val_2217_);
lean_dec_ref(v_P_2198_);
lean_dec_ref(v_lhs_2194_);
v_toCold_2304_ = lean_ctor_get(v___y_2207_, 0);
v_inheritedTraceOptions_2305_ = lean_ctor_get(v_toCold_2304_, 11);
lean_inc(v___y_2208_);
lean_inc_ref(v___y_2207_);
lean_inc(v___y_2206_);
lean_inc_ref(v___y_2205_);
lean_inc(v___y_2204_);
lean_inc_ref(v___y_2203_);
lean_inc(v___y_2202_);
lean_inc_ref(v___y_2201_);
lean_inc(v___y_2200_);
lean_inc_ref(v_inheritedTraceOptions_2305_);
v___x_2306_ = lean_apply_11(v___f_2196_, v_inheritedTraceOptions_2305_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, lean_box(0));
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; uint8_t v___x_2308_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2308_ = lean_unbox(v_a_2307_);
lean_dec(v_a_2307_);
if (v___x_2308_ == 0)
{
lean_dec(v_cls_2197_);
lean_dec_ref(v_rhs_2195_);
goto v___jp_2210_;
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2309_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2310_ = l_Lean_indentExpr(v_rhs_2195_);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2197_, v___x_2311_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_dec_ref_known(v___x_2312_, 1);
goto v___jp_2210_;
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_cls_2197_);
lean_dec_ref(v_rhs_2195_);
v_a_2321_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2306_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2306_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
else
{
lean_object* v_toCold_2329_; lean_object* v_inheritedTraceOptions_2330_; lean_object* v___x_2331_; 
lean_dec(v___x_2216_);
lean_dec_ref(v_P_2198_);
lean_dec_ref(v_rhs_2195_);
v_toCold_2329_ = lean_ctor_get(v___y_2207_, 0);
v_inheritedTraceOptions_2330_ = lean_ctor_get(v_toCold_2329_, 11);
lean_inc(v___y_2208_);
lean_inc_ref(v___y_2207_);
lean_inc(v___y_2206_);
lean_inc_ref(v___y_2205_);
lean_inc(v___y_2204_);
lean_inc_ref(v___y_2203_);
lean_inc(v___y_2202_);
lean_inc_ref(v___y_2201_);
lean_inc(v___y_2200_);
lean_inc_ref(v_inheritedTraceOptions_2330_);
v___x_2331_ = lean_apply_11(v___f_2196_, v_inheritedTraceOptions_2330_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, lean_box(0));
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; uint8_t v___x_2333_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = lean_unbox(v_a_2332_);
lean_dec(v_a_2332_);
if (v___x_2333_ == 0)
{
lean_dec(v_cls_2197_);
lean_dec_ref(v_lhs_2194_);
goto v___jp_2213_;
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2334_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2335_ = l_Lean_indentExpr(v_lhs_2194_);
v___x_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2197_, v___x_2336_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_dec_ref_known(v___x_2337_, 1);
goto v___jp_2213_;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_cls_2197_);
lean_dec_ref(v_lhs_2194_);
v_a_2346_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2331_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2331_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
v___jp_2210_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
return v___x_2212_;
}
v___jp_2213_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___boxed(lean_object* v_lhs_2354_, lean_object* v_rhs_2355_, lean_object* v___f_2356_, lean_object* v_cls_2357_, lean_object* v_P_2358_, lean_object* v_____r_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2354_, v_rhs_2355_, v___f_2356_, v_cls_2357_, v_P_2358_, v_____r_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(lean_object* v_lhs_2371_, lean_object* v_rhs_2372_, uint8_t v___x_2373_, lean_object* v___f_2374_, lean_object* v_cls_2375_, lean_object* v_P_2376_, lean_object* v_____r_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2371_);
if (lean_obj_tag(v___x_2397_) == 1)
{
lean_object* v_val_2398_; lean_object* v___x_2399_; 
v_val_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_val_2398_);
lean_dec_ref_known(v___x_2397_, 1);
v___x_2399_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2372_);
if (lean_obj_tag(v___x_2399_) == 1)
{
lean_object* v_val_2400_; uint8_t v___x_2401_; 
v_val_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_val_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v___x_2401_ = lean_expr_eqv(v_val_2398_, v_val_2400_);
if (v___x_2401_ == 0)
{
lean_object* v_toCold_2402_; lean_object* v_inheritedTraceOptions_2403_; lean_object* v___x_2404_; 
lean_dec_ref(v_P_2376_);
v_toCold_2402_ = lean_ctor_get(v___y_2385_, 0);
v_inheritedTraceOptions_2403_ = lean_ctor_get(v_toCold_2402_, 11);
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
lean_inc(v___y_2384_);
lean_inc_ref(v___y_2383_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v___y_2378_);
lean_inc_ref(v_inheritedTraceOptions_2403_);
v___x_2404_ = lean_apply_11(v___f_2374_, v_inheritedTraceOptions_2403_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, lean_box(0));
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; uint8_t v___x_2406_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v___x_2406_ = lean_unbox(v_a_2405_);
lean_dec(v_a_2405_);
if (v___x_2406_ == 0)
{
lean_dec(v_val_2400_);
lean_dec(v_val_2398_);
lean_dec(v_cls_2375_);
lean_dec_ref(v_rhs_2372_);
lean_dec_ref(v_lhs_2371_);
goto v___jp_2388_;
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2407_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2);
v___x_2408_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2398_);
v___x_2409_ = l_Lean_MessageData_ofExpr(v___x_2408_);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2407_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = l_Lean_indentExpr(v_lhs_2371_);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6);
v___x_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2400_);
v___x_2418_ = l_Lean_MessageData_ofExpr(v___x_2417_);
v___x_2419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2416_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v___x_2411_);
v___x_2421_ = l_Lean_indentExpr(v_rhs_2372_);
v___x_2422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2420_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2375_, v___x_2422_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_dec_ref_known(v___x_2423_, 1);
goto v___jp_2388_;
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec(v_val_2400_);
lean_dec(v_val_2398_);
lean_dec(v_cls_2375_);
lean_dec_ref(v_rhs_2372_);
lean_dec_ref(v_lhs_2371_);
v_a_2432_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2404_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2404_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
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
}
else
{
lean_object* v_toCold_2440_; lean_object* v_options_2441_; lean_object* v_inheritedTraceOptions_2442_; uint8_t v_hasTrace_2443_; lean_object* v___x_2444_; lean_object* v___f_2445_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; 
lean_dec(v_val_2400_);
lean_dec_ref(v___f_2374_);
v_toCold_2440_ = lean_ctor_get(v___y_2385_, 0);
v_options_2441_ = lean_ctor_get(v_toCold_2440_, 2);
v_inheritedTraceOptions_2442_ = lean_ctor_get(v_toCold_2440_, 11);
v_hasTrace_2443_ = lean_ctor_get_uint8(v_options_2441_, sizeof(void*)*1);
v___x_2444_ = lean_box(v___x_2373_);
lean_inc(v_val_2398_);
v___f_2445_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_2445_, 0, v_val_2398_);
lean_closure_set(v___f_2445_, 1, v_lhs_2371_);
lean_closure_set(v___f_2445_, 2, v_rhs_2372_);
lean_closure_set(v___f_2445_, 3, v_P_2376_);
lean_closure_set(v___f_2445_, 4, v___x_2444_);
if (v_hasTrace_2443_ == 0)
{
lean_dec(v_cls_2375_);
v___y_2447_ = v___y_2381_;
v___y_2448_ = v___y_2382_;
v___y_2449_ = v___y_2383_;
v___y_2450_ = v___y_2384_;
v___y_2451_ = v___y_2385_;
v___y_2452_ = v___y_2386_;
goto v___jp_2446_;
}
else
{
lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__5));
lean_inc(v_cls_2375_);
v___x_2458_ = l_Lean_Name_append(v___x_2457_, v_cls_2375_);
v___x_2459_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2442_, v_options_2441_, v___x_2458_);
lean_dec(v___x_2458_);
if (v___x_2459_ == 0)
{
lean_dec(v_cls_2375_);
v___y_2447_ = v___y_2381_;
v___y_2448_ = v___y_2382_;
v___y_2449_ = v___y_2383_;
v___y_2450_ = v___y_2384_;
v___y_2451_ = v___y_2385_;
v___y_2452_ = v___y_2386_;
goto v___jp_2446_;
}
else
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2460_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11);
lean_inc(v_val_2398_);
v___x_2461_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2398_);
v___x_2462_ = l_Lean_MessageData_ofExpr(v___x_2461_);
v___x_2463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2460_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13);
v___x_2465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2375_, v___x_2465_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_dec_ref_known(v___x_2466_, 1);
v___y_2447_ = v___y_2381_;
v___y_2448_ = v___y_2382_;
v___y_2449_ = v___y_2383_;
v___y_2450_ = v___y_2384_;
v___y_2451_ = v___y_2385_;
v___y_2452_ = v___y_2386_;
goto v___jp_2446_;
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec_ref(v___f_2445_);
lean_dec(v_val_2398_);
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
v___jp_2446_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2453_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8);
v___x_2454_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9));
v___x_2455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2455_, 0, v_val_2398_);
lean_ctor_set(v___x_2455_, 1, v___x_2453_);
lean_ctor_set(v___x_2455_, 2, v___x_2454_);
v___x_2456_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___f_2445_, v___x_2455_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2456_;
}
}
}
else
{
lean_object* v_toCold_2475_; lean_object* v_inheritedTraceOptions_2476_; lean_object* v___x_2477_; 
lean_dec(v___x_2399_);
lean_dec(v_val_2398_);
lean_dec_ref(v_P_2376_);
lean_dec_ref(v_lhs_2371_);
v_toCold_2475_ = lean_ctor_get(v___y_2385_, 0);
v_inheritedTraceOptions_2476_ = lean_ctor_get(v_toCold_2475_, 11);
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
lean_inc(v___y_2384_);
lean_inc_ref(v___y_2383_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v___y_2378_);
lean_inc_ref(v_inheritedTraceOptions_2476_);
v___x_2477_ = lean_apply_11(v___f_2374_, v_inheritedTraceOptions_2476_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, lean_box(0));
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; uint8_t v___x_2479_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
v___x_2479_ = lean_unbox(v_a_2478_);
lean_dec(v_a_2478_);
if (v___x_2479_ == 0)
{
lean_dec(v_cls_2375_);
lean_dec_ref(v_rhs_2372_);
goto v___jp_2391_;
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2480_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2481_ = l_Lean_indentExpr(v_rhs_2372_);
v___x_2482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2480_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2375_, v___x_2482_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_dec_ref_known(v___x_2483_, 1);
goto v___jp_2391_;
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v_cls_2375_);
lean_dec_ref(v_rhs_2372_);
v_a_2492_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2477_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2477_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
}
else
{
lean_object* v_toCold_2500_; lean_object* v_inheritedTraceOptions_2501_; lean_object* v___x_2502_; 
lean_dec(v___x_2397_);
lean_dec_ref(v_P_2376_);
lean_dec_ref(v_rhs_2372_);
v_toCold_2500_ = lean_ctor_get(v___y_2385_, 0);
v_inheritedTraceOptions_2501_ = lean_ctor_get(v_toCold_2500_, 11);
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
lean_inc(v___y_2384_);
lean_inc_ref(v___y_2383_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v___y_2378_);
lean_inc_ref(v_inheritedTraceOptions_2501_);
v___x_2502_ = lean_apply_11(v___f_2374_, v_inheritedTraceOptions_2501_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, lean_box(0));
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; uint8_t v___x_2504_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2502_, 1);
v___x_2504_ = lean_unbox(v_a_2503_);
lean_dec(v_a_2503_);
if (v___x_2504_ == 0)
{
lean_dec(v_cls_2375_);
lean_dec_ref(v_lhs_2371_);
goto v___jp_2394_;
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2505_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2506_ = l_Lean_indentExpr(v_lhs_2371_);
v___x_2507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2375_, v___x_2507_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_dec_ref_known(v___x_2508_, 1);
goto v___jp_2394_;
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec(v_cls_2375_);
lean_dec_ref(v_lhs_2371_);
v_a_2517_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2502_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2502_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
v___jp_2388_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2389_, 0, v___x_2373_);
lean_ctor_set_uint8(v___x_2389_, 1, v___x_2373_);
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
return v___x_2390_;
}
v___jp_2391_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2392_, 0, v___x_2373_);
lean_ctor_set_uint8(v___x_2392_, 1, v___x_2373_);
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
return v___x_2393_;
}
v___jp_2394_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2395_, 0, v___x_2373_);
lean_ctor_set_uint8(v___x_2395_, 1, v___x_2373_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
return v___x_2396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7___boxed(lean_object** _args){
lean_object* v_lhs_2525_ = _args[0];
lean_object* v_rhs_2526_ = _args[1];
lean_object* v___x_2527_ = _args[2];
lean_object* v___f_2528_ = _args[3];
lean_object* v_cls_2529_ = _args[4];
lean_object* v_P_2530_ = _args[5];
lean_object* v_____r_2531_ = _args[6];
lean_object* v___y_2532_ = _args[7];
lean_object* v___y_2533_ = _args[8];
lean_object* v___y_2534_ = _args[9];
lean_object* v___y_2535_ = _args[10];
lean_object* v___y_2536_ = _args[11];
lean_object* v___y_2537_ = _args[12];
lean_object* v___y_2538_ = _args[13];
lean_object* v___y_2539_ = _args[14];
lean_object* v___y_2540_ = _args[15];
lean_object* v___y_2541_ = _args[16];
_start:
{
uint8_t v___x_188845__boxed_2542_; lean_object* v_res_2543_; 
v___x_188845__boxed_2542_ = lean_unbox(v___x_2527_);
v_res_2543_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(v_lhs_2525_, v_rhs_2526_, v___x_188845__boxed_2542_, v___f_2528_, v_cls_2529_, v_P_2530_, v_____r_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
return v_res_2543_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(lean_object* v_e_2544_){
_start:
{
if (lean_obj_tag(v_e_2544_) == 0)
{
uint8_t v___x_2545_; 
v___x_2545_ = 2;
return v___x_2545_;
}
else
{
uint8_t v___x_2546_; 
v___x_2546_ = 0;
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5___boxed(lean_object* v_e_2547_){
_start:
{
uint8_t v_res_2548_; lean_object* v_r_2549_; 
v_res_2548_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_e_2547_);
lean_dec_ref(v_e_2547_);
v_r_2549_ = lean_box(v_res_2548_);
return v_r_2549_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(lean_object* v_x_2550_){
_start:
{
if (lean_obj_tag(v_x_2550_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
v_a_2552_ = lean_ctor_get(v_x_2550_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_x_2550_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v_x_2550_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v_x_2550_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
lean_ctor_set_tag(v___x_2554_, 1);
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
v_a_2560_ = lean_ctor_get(v_x_2550_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_x_2550_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v_x_2550_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v_x_2550_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set_tag(v___x_2562_, 0);
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg___boxed(lean_object* v_x_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_2568_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(lean_object* v_opts_2571_, lean_object* v_opt_2572_){
_start:
{
lean_object* v_name_2573_; lean_object* v_defValue_2574_; lean_object* v_map_2575_; lean_object* v___x_2576_; 
v_name_2573_ = lean_ctor_get(v_opt_2572_, 0);
v_defValue_2574_ = lean_ctor_get(v_opt_2572_, 1);
v_map_2575_ = lean_ctor_get(v_opts_2571_, 0);
v___x_2576_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2575_, v_name_2573_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_inc(v_defValue_2574_);
return v_defValue_2574_;
}
else
{
lean_object* v_val_2577_; 
v_val_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_val_2577_);
lean_dec_ref_known(v___x_2576_, 1);
if (lean_obj_tag(v_val_2577_) == 3)
{
lean_object* v_v_2578_; 
v_v_2578_ = lean_ctor_get(v_val_2577_, 0);
lean_inc(v_v_2578_);
lean_dec_ref_known(v_val_2577_, 1);
return v_v_2578_;
}
else
{
lean_dec(v_val_2577_);
lean_inc(v_defValue_2574_);
return v_defValue_2574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6___boxed(lean_object* v_opts_2579_, lean_object* v_opt_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2579_, v_opt_2580_);
lean_dec_ref(v_opt_2580_);
lean_dec_ref(v_opts_2579_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(size_t v_sz_2582_, size_t v_i_2583_, lean_object* v_bs_2584_){
_start:
{
uint8_t v___x_2585_; 
v___x_2585_ = lean_usize_dec_lt(v_i_2583_, v_sz_2582_);
if (v___x_2585_ == 0)
{
return v_bs_2584_;
}
else
{
lean_object* v_v_2586_; lean_object* v_msg_2587_; lean_object* v___x_2588_; lean_object* v_bs_x27_2589_; size_t v___x_2590_; size_t v___x_2591_; lean_object* v___x_2592_; 
v_v_2586_ = lean_array_uget_borrowed(v_bs_2584_, v_i_2583_);
v_msg_2587_ = lean_ctor_get(v_v_2586_, 1);
lean_inc_ref(v_msg_2587_);
v___x_2588_ = lean_unsigned_to_nat(0u);
v_bs_x27_2589_ = lean_array_uset(v_bs_2584_, v_i_2583_, v___x_2588_);
v___x_2590_ = ((size_t)1ULL);
v___x_2591_ = lean_usize_add(v_i_2583_, v___x_2590_);
v___x_2592_ = lean_array_uset(v_bs_x27_2589_, v_i_2583_, v_msg_2587_);
v_i_2583_ = v___x_2591_;
v_bs_2584_ = v___x_2592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_2594_, lean_object* v_i_2595_, lean_object* v_bs_2596_){
_start:
{
size_t v_sz_boxed_2597_; size_t v_i_boxed_2598_; lean_object* v_res_2599_; 
v_sz_boxed_2597_ = lean_unbox_usize(v_sz_2594_);
lean_dec(v_sz_2594_);
v_i_boxed_2598_ = lean_unbox_usize(v_i_2595_);
lean_dec(v_i_2595_);
v_res_2599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_boxed_2597_, v_i_boxed_2598_, v_bs_2596_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(lean_object* v_oldTraces_2600_, lean_object* v_data_2601_, lean_object* v_ref_2602_, lean_object* v_msg_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v_toCold_2609_; lean_object* v_currRecDepth_2610_; lean_object* v_ref_2611_; uint16_t v_optionFlags_2612_; uint8_t v_suppressElabErrors_2613_; uint8_t v_checkDeprecated_2614_; uint8_t v_isRecordingDeps_2615_; lean_object* v_ref_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v_traceState_2619_; lean_object* v_traces_2620_; lean_object* v___x_2621_; size_t v_sz_2622_; size_t v___x_2623_; lean_object* v___x_2624_; lean_object* v_msg_2625_; lean_object* v___x_2626_; lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2665_; 
v_toCold_2609_ = lean_ctor_get(v___y_2606_, 0);
v_currRecDepth_2610_ = lean_ctor_get(v___y_2606_, 1);
v_ref_2611_ = lean_ctor_get(v___y_2606_, 2);
v_optionFlags_2612_ = lean_ctor_get_uint16(v___y_2606_, sizeof(void*)*3);
v_suppressElabErrors_2613_ = lean_ctor_get_uint8(v___y_2606_, sizeof(void*)*3 + 2);
v_checkDeprecated_2614_ = lean_ctor_get_uint8(v___y_2606_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2615_ = lean_ctor_get_uint8(v___y_2606_, sizeof(void*)*3 + 4);
v_ref_2616_ = l_Lean_replaceRef(v_ref_2602_, v_ref_2611_);
lean_inc(v_currRecDepth_2610_);
lean_inc_ref(v_toCold_2609_);
v___x_2617_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2617_, 0, v_toCold_2609_);
lean_ctor_set(v___x_2617_, 1, v_currRecDepth_2610_);
lean_ctor_set(v___x_2617_, 2, v_ref_2616_);
lean_ctor_set_uint16(v___x_2617_, sizeof(void*)*3, v_optionFlags_2612_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*3 + 2, v_suppressElabErrors_2613_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*3 + 3, v_checkDeprecated_2614_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*3 + 4, v_isRecordingDeps_2615_);
v___x_2618_ = lean_st_ref_get(v___y_2607_);
v_traceState_2619_ = lean_ctor_get(v___x_2618_, 4);
lean_inc_ref(v_traceState_2619_);
lean_dec(v___x_2618_);
v_traces_2620_ = lean_ctor_get(v_traceState_2619_, 0);
lean_inc_ref(v_traces_2620_);
lean_dec_ref(v_traceState_2619_);
v___x_2621_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2620_);
lean_dec_ref(v_traces_2620_);
v_sz_2622_ = lean_array_size(v___x_2621_);
v___x_2623_ = ((size_t)0ULL);
v___x_2624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3_spec__4(v_sz_2622_, v___x_2623_, v___x_2621_);
v_msg_2625_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2625_, 0, v_data_2601_);
lean_ctor_set(v_msg_2625_, 1, v_msg_2603_);
lean_ctor_set(v_msg_2625_, 2, v___x_2624_);
v___x_2626_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_2625_, v___y_2604_, v___y_2605_, v___x_2617_, v___y_2607_);
lean_dec_ref_known(v___x_2617_, 3);
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2665_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2665_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v_traceState_2632_; lean_object* v_env_2633_; lean_object* v_nextMacroScope_2634_; lean_object* v_ngen_2635_; lean_object* v_auxDeclNGen_2636_; lean_object* v_cache_2637_; lean_object* v_recordedDeps_2638_; lean_object* v_messages_2639_; lean_object* v_infoState_2640_; lean_object* v_snapshotTasks_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2664_; 
v___x_2631_ = lean_st_ref_take(v___y_2607_);
v_traceState_2632_ = lean_ctor_get(v___x_2631_, 4);
v_env_2633_ = lean_ctor_get(v___x_2631_, 0);
v_nextMacroScope_2634_ = lean_ctor_get(v___x_2631_, 1);
v_ngen_2635_ = lean_ctor_get(v___x_2631_, 2);
v_auxDeclNGen_2636_ = lean_ctor_get(v___x_2631_, 3);
v_cache_2637_ = lean_ctor_get(v___x_2631_, 5);
v_recordedDeps_2638_ = lean_ctor_get(v___x_2631_, 6);
v_messages_2639_ = lean_ctor_get(v___x_2631_, 7);
v_infoState_2640_ = lean_ctor_get(v___x_2631_, 8);
v_snapshotTasks_2641_ = lean_ctor_get(v___x_2631_, 9);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2643_ = v___x_2631_;
v_isShared_2644_ = v_isSharedCheck_2664_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_snapshotTasks_2641_);
lean_inc(v_infoState_2640_);
lean_inc(v_messages_2639_);
lean_inc(v_recordedDeps_2638_);
lean_inc(v_cache_2637_);
lean_inc(v_traceState_2632_);
lean_inc(v_auxDeclNGen_2636_);
lean_inc(v_ngen_2635_);
lean_inc(v_nextMacroScope_2634_);
lean_inc(v_env_2633_);
lean_dec(v___x_2631_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2664_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
uint64_t v_tid_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2662_; 
v_tid_2645_ = lean_ctor_get_uint64(v_traceState_2632_, sizeof(void*)*1);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_traceState_2632_);
if (v_isSharedCheck_2662_ == 0)
{
lean_object* v_unused_2663_; 
v_unused_2663_ = lean_ctor_get(v_traceState_2632_, 0);
lean_dec(v_unused_2663_);
v___x_2647_ = v_traceState_2632_;
v_isShared_2648_ = v_isSharedCheck_2662_;
goto v_resetjp_2646_;
}
else
{
lean_dec(v_traceState_2632_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2662_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2649_ = lean_box(0);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v_ref_2602_);
lean_ctor_set(v___x_2650_, 1, v_a_2627_);
v___x_2651_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2600_, v___x_2650_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2651_);
v___x_2653_ = v___x_2647_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2651_);
lean_ctor_set_uint64(v_reuseFailAlloc_2661_, sizeof(void*)*1, v_tid_2645_);
v___x_2653_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2655_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 4, v___x_2653_);
v___x_2655_ = v___x_2643_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_env_2633_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_nextMacroScope_2634_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_ngen_2635_);
lean_ctor_set(v_reuseFailAlloc_2660_, 3, v_auxDeclNGen_2636_);
lean_ctor_set(v_reuseFailAlloc_2660_, 4, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2660_, 5, v_cache_2637_);
lean_ctor_set(v_reuseFailAlloc_2660_, 6, v_recordedDeps_2638_);
lean_ctor_set(v_reuseFailAlloc_2660_, 7, v_messages_2639_);
lean_ctor_set(v_reuseFailAlloc_2660_, 8, v_infoState_2640_);
lean_ctor_set(v_reuseFailAlloc_2660_, 9, v_snapshotTasks_2641_);
v___x_2655_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2656_ = lean_st_ref_put(v___y_2607_, v___x_2655_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2649_);
v___x_2658_ = v___x_2629_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2649_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg___boxed(lean_object* v_oldTraces_2666_, lean_object* v_data_2667_, lean_object* v_ref_2668_, lean_object* v_msg_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2666_, v_data_2667_, v_ref_2668_, v_msg_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
return v_res_2675_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__0));
v___x_2678_ = l_Lean_stringToMessageData(v___x_2677_);
return v___x_2678_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2679_; double v___x_2680_; 
v___x_2679_ = lean_unsigned_to_nat(1000u);
v___x_2680_ = lean_float_of_nat(v___x_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(lean_object* v_cls_2681_, uint8_t v_collapsed_2682_, lean_object* v_tag_2683_, lean_object* v_opts_2684_, uint8_t v_clsEnabled_2685_, lean_object* v_oldTraces_2686_, lean_object* v_msg_2687_, lean_object* v_resStartStop_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_fst_2699_; lean_object* v_snd_2700_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v_data_2704_; lean_object* v_fst_2715_; lean_object* v_snd_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; lean_object* v___y_2720_; lean_object* v_a_2721_; uint8_t v___y_2736_; double v___y_2768_; 
v_fst_2699_ = lean_ctor_get(v_resStartStop_2688_, 0);
lean_inc(v_fst_2699_);
v_snd_2700_ = lean_ctor_get(v_resStartStop_2688_, 1);
lean_inc(v_snd_2700_);
lean_dec_ref(v_resStartStop_2688_);
v_fst_2715_ = lean_ctor_get(v_snd_2700_, 0);
lean_inc(v_fst_2715_);
v_snd_2716_ = lean_ctor_get(v_snd_2700_, 1);
lean_inc(v_snd_2716_);
lean_dec(v_snd_2700_);
v___x_2717_ = l_Lean_trace_profiler;
v___x_2718_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2684_, v___x_2717_);
if (v___x_2718_ == 0)
{
v___y_2736_ = v___x_2718_;
goto v___jp_2735_;
}
else
{
lean_object* v___x_2773_; uint8_t v___x_2774_; 
v___x_2773_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2774_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_opts_2684_, v___x_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2776_; double v___x_2777_; double v___x_2778_; double v___x_2779_; 
v___x_2775_ = l_Lean_trace_profiler_threshold;
v___x_2776_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2684_, v___x_2775_);
v___x_2777_ = lean_float_of_nat(v___x_2776_);
v___x_2778_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__2);
v___x_2779_ = lean_float_div(v___x_2777_, v___x_2778_);
v___y_2768_ = v___x_2779_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2780_; lean_object* v___x_2781_; double v___x_2782_; 
v___x_2780_ = l_Lean_trace_profiler_threshold;
v___x_2781_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__6(v_opts_2684_, v___x_2780_);
v___x_2782_ = lean_float_of_nat(v___x_2781_);
v___y_2768_ = v___x_2782_;
goto v___jp_2767_;
}
}
v___jp_2701_:
{
lean_object* v___x_2705_; 
lean_inc(v___y_2703_);
v___x_2705_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_2686_, v_data_2704_, v___y_2703_, v___y_2702_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v___x_2706_; 
lean_dec_ref_known(v___x_2705_, 1);
v___x_2706_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2699_);
return v___x_2706_;
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v_fst_2699_);
v_a_2707_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2705_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2705_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
v___jp_2719_:
{
uint8_t v_result_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; double v___x_2725_; lean_object* v_data_2726_; 
v_result_2722_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__5(v_fst_2699_);
v___x_2723_ = lean_box(v_result_2722_);
v___x_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
v___x_2725_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2683_);
lean_inc_ref(v___x_2724_);
lean_inc(v_cls_2681_);
v_data_2726_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2726_, 0, v_cls_2681_);
lean_ctor_set(v_data_2726_, 1, v___x_2724_);
lean_ctor_set(v_data_2726_, 2, v_tag_2683_);
lean_ctor_set_float(v_data_2726_, sizeof(void*)*3, v___x_2725_);
lean_ctor_set_float(v_data_2726_, sizeof(void*)*3 + 8, v___x_2725_);
lean_ctor_set_uint8(v_data_2726_, sizeof(void*)*3 + 16, v_collapsed_2682_);
if (v___x_2718_ == 0)
{
lean_dec_ref_known(v___x_2724_, 1);
lean_dec(v_snd_2716_);
lean_dec(v_fst_2715_);
lean_dec_ref(v_tag_2683_);
lean_dec(v_cls_2681_);
v___y_2702_ = v_a_2721_;
v___y_2703_ = v___y_2720_;
v_data_2704_ = v_data_2726_;
goto v___jp_2701_;
}
else
{
lean_object* v_data_2727_; double v___x_2728_; double v___x_2729_; 
lean_dec_ref_known(v_data_2726_, 3);
v_data_2727_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2727_, 0, v_cls_2681_);
lean_ctor_set(v_data_2727_, 1, v___x_2724_);
lean_ctor_set(v_data_2727_, 2, v_tag_2683_);
v___x_2728_ = lean_unbox_float(v_fst_2715_);
lean_dec(v_fst_2715_);
lean_ctor_set_float(v_data_2727_, sizeof(void*)*3, v___x_2728_);
v___x_2729_ = lean_unbox_float(v_snd_2716_);
lean_dec(v_snd_2716_);
lean_ctor_set_float(v_data_2727_, sizeof(void*)*3 + 8, v___x_2729_);
lean_ctor_set_uint8(v_data_2727_, sizeof(void*)*3 + 16, v_collapsed_2682_);
v___y_2702_ = v_a_2721_;
v___y_2703_ = v___y_2720_;
v_data_2704_ = v_data_2727_;
goto v___jp_2701_;
}
}
v___jp_2730_:
{
lean_object* v_ref_2731_; lean_object* v___x_2732_; 
v_ref_2731_ = lean_ctor_get(v___y_2696_, 2);
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc(v___y_2693_);
lean_inc_ref(v___y_2692_);
lean_inc(v___y_2691_);
lean_inc_ref(v___y_2690_);
lean_inc(v___y_2689_);
lean_inc(v_fst_2699_);
v___x_2732_ = lean_apply_11(v_msg_2687_, v_fst_2699_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___y_2720_ = v_ref_2731_;
v_a_2721_ = v_a_2733_;
goto v___jp_2719_;
}
else
{
lean_object* v___x_2734_; 
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___closed__1);
v___y_2720_ = v_ref_2731_;
v_a_2721_ = v___x_2734_;
goto v___jp_2719_;
}
}
v___jp_2735_:
{
if (v_clsEnabled_2685_ == 0)
{
if (v___y_2736_ == 0)
{
lean_object* v___x_2737_; lean_object* v_traceState_2738_; lean_object* v_env_2739_; lean_object* v_nextMacroScope_2740_; lean_object* v_ngen_2741_; lean_object* v_auxDeclNGen_2742_; lean_object* v_cache_2743_; lean_object* v_recordedDeps_2744_; lean_object* v_messages_2745_; lean_object* v_infoState_2746_; lean_object* v_snapshotTasks_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v_snd_2716_);
lean_dec(v_fst_2715_);
lean_dec_ref(v_msg_2687_);
lean_dec_ref(v_tag_2683_);
lean_dec(v_cls_2681_);
v___x_2737_ = lean_st_ref_take(v___y_2697_);
v_traceState_2738_ = lean_ctor_get(v___x_2737_, 4);
v_env_2739_ = lean_ctor_get(v___x_2737_, 0);
v_nextMacroScope_2740_ = lean_ctor_get(v___x_2737_, 1);
v_ngen_2741_ = lean_ctor_get(v___x_2737_, 2);
v_auxDeclNGen_2742_ = lean_ctor_get(v___x_2737_, 3);
v_cache_2743_ = lean_ctor_get(v___x_2737_, 5);
v_recordedDeps_2744_ = lean_ctor_get(v___x_2737_, 6);
v_messages_2745_ = lean_ctor_get(v___x_2737_, 7);
v_infoState_2746_ = lean_ctor_get(v___x_2737_, 8);
v_snapshotTasks_2747_ = lean_ctor_get(v___x_2737_, 9);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2749_ = v___x_2737_;
v_isShared_2750_ = v_isSharedCheck_2766_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_snapshotTasks_2747_);
lean_inc(v_infoState_2746_);
lean_inc(v_messages_2745_);
lean_inc(v_recordedDeps_2744_);
lean_inc(v_cache_2743_);
lean_inc(v_traceState_2738_);
lean_inc(v_auxDeclNGen_2742_);
lean_inc(v_ngen_2741_);
lean_inc(v_nextMacroScope_2740_);
lean_inc(v_env_2739_);
lean_dec(v___x_2737_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2766_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
uint64_t v_tid_2751_; lean_object* v_traces_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2765_; 
v_tid_2751_ = lean_ctor_get_uint64(v_traceState_2738_, sizeof(void*)*1);
v_traces_2752_ = lean_ctor_get(v_traceState_2738_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v_traceState_2738_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2754_ = v_traceState_2738_;
v_isShared_2755_ = v_isSharedCheck_2765_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_traces_2752_);
lean_dec(v_traceState_2738_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2765_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2686_, v_traces_2752_);
lean_dec_ref(v_traces_2752_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2756_);
v___x_2758_ = v___x_2754_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2756_);
lean_ctor_set_uint64(v_reuseFailAlloc_2764_, sizeof(void*)*1, v_tid_2751_);
v___x_2758_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2760_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 4, v___x_2758_);
v___x_2760_ = v___x_2749_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_env_2739_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_nextMacroScope_2740_);
lean_ctor_set(v_reuseFailAlloc_2763_, 2, v_ngen_2741_);
lean_ctor_set(v_reuseFailAlloc_2763_, 3, v_auxDeclNGen_2742_);
lean_ctor_set(v_reuseFailAlloc_2763_, 4, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2763_, 5, v_cache_2743_);
lean_ctor_set(v_reuseFailAlloc_2763_, 6, v_recordedDeps_2744_);
lean_ctor_set(v_reuseFailAlloc_2763_, 7, v_messages_2745_);
lean_ctor_set(v_reuseFailAlloc_2763_, 8, v_infoState_2746_);
lean_ctor_set(v_reuseFailAlloc_2763_, 9, v_snapshotTasks_2747_);
v___x_2760_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = lean_st_ref_put(v___y_2697_, v___x_2760_);
v___x_2762_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_fst_2699_);
return v___x_2762_;
}
}
}
}
}
else
{
goto v___jp_2730_;
}
}
else
{
goto v___jp_2730_;
}
}
v___jp_2767_:
{
double v___x_2769_; double v___x_2770_; double v___x_2771_; uint8_t v___x_2772_; 
v___x_2769_ = lean_unbox_float(v_snd_2716_);
v___x_2770_ = lean_unbox_float(v_fst_2715_);
v___x_2771_ = lean_float_sub(v___x_2769_, v___x_2770_);
v___x_2772_ = lean_float_decLt(v___y_2768_, v___x_2771_);
v___y_2736_ = v___x_2772_;
goto v___jp_2735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3___boxed(lean_object** _args){
lean_object* v_cls_2783_ = _args[0];
lean_object* v_collapsed_2784_ = _args[1];
lean_object* v_tag_2785_ = _args[2];
lean_object* v_opts_2786_ = _args[3];
lean_object* v_clsEnabled_2787_ = _args[4];
lean_object* v_oldTraces_2788_ = _args[5];
lean_object* v_msg_2789_ = _args[6];
lean_object* v_resStartStop_2790_ = _args[7];
lean_object* v___y_2791_ = _args[8];
lean_object* v___y_2792_ = _args[9];
lean_object* v___y_2793_ = _args[10];
lean_object* v___y_2794_ = _args[11];
lean_object* v___y_2795_ = _args[12];
lean_object* v___y_2796_ = _args[13];
lean_object* v___y_2797_ = _args[14];
lean_object* v___y_2798_ = _args[15];
lean_object* v___y_2799_ = _args[16];
lean_object* v___y_2800_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2801_; uint8_t v_clsEnabled_boxed_2802_; lean_object* v_res_2803_; 
v_collapsed_boxed_2801_ = lean_unbox(v_collapsed_2784_);
v_clsEnabled_boxed_2802_ = lean_unbox(v_clsEnabled_2787_);
v_res_2803_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2783_, v_collapsed_boxed_2801_, v_tag_2785_, v_opts_2786_, v_clsEnabled_boxed_2802_, v_oldTraces_2788_, v_msg_2789_, v_resStartStop_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v_opts_2786_);
return v_res_2803_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__1));
v___x_2808_ = l_Lean_stringToMessageData(v___x_2807_);
return v___x_2808_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4(void){
_start:
{
lean_object* v___x_2810_; double v___x_2811_; 
v___x_2810_ = lean_unsigned_to_nat(1000000000u);
v___x_2811_ = lean_float_of_nat(v___x_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(lean_object* v_P_2812_, lean_object* v_lhs_2813_, lean_object* v_rhs_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
uint8_t v___y_2826_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v_toCold_2848_; lean_object* v_options_2849_; lean_object* v_inheritedTraceOptions_2850_; uint8_t v_hasTrace_2851_; lean_object* v_cls_2852_; lean_object* v___f_2853_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; uint8_t v_____do__lift_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; 
v_toCold_2848_ = lean_ctor_get(v_a_2822_, 0);
v_options_2849_ = lean_ctor_get(v_toCold_2848_, 2);
v_inheritedTraceOptions_2850_ = lean_ctor_get(v_toCold_2848_, 11);
v_hasTrace_2851_ = lean_ctor_get_uint8(v_options_2849_, sizeof(void*)*1);
v_cls_2852_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___f_2853_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__0));
if (v_hasTrace_2851_ == 0)
{
lean_object* v___x_2981_; lean_object* v_a_2982_; uint8_t v___x_2983_; 
v___x_2981_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2852_, v_inheritedTraceOptions_2850_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref(v___x_2981_);
v___x_2983_ = lean_unbox(v_a_2982_);
lean_dec(v_a_2982_);
v_____do__lift_2958_ = v___x_2983_;
v___y_2959_ = v_a_2815_;
v___y_2960_ = v_a_2816_;
v___y_2961_ = v_a_2817_;
v___y_2962_ = v_a_2818_;
v___y_2963_ = v_a_2819_;
v___y_2964_ = v_a_2820_;
v___y_2965_ = v_a_2821_;
v___y_2966_ = v_a_2822_;
v___y_2967_ = v_a_2823_;
goto v___jp_2957_;
}
else
{
lean_object* v___f_2984_; uint8_t v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v_a_2992_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v_a_3004_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v_a_3022_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v_a_3037_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; 
v___f_2984_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__3));
v___x_2985_ = 0;
v___x_2986_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_2987_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_2988_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2850_, v_options_2849_, v___x_2987_);
if (v___x_2988_ == 0)
{
lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = l_Lean_trace_profiler;
v___x_3086_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_2849_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v_a_3088_; uint8_t v___x_3089_; 
v___x_3087_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2852_, v_inheritedTraceOptions_2850_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3088_);
lean_dec_ref(v___x_3087_);
v___x_3089_ = lean_unbox(v_a_3088_);
lean_dec(v_a_3088_);
v_____do__lift_2958_ = v___x_3089_;
v___y_2959_ = v_a_2815_;
v___y_2960_ = v_a_2816_;
v___y_2961_ = v_a_2817_;
v___y_2962_ = v_a_2818_;
v___y_2963_ = v_a_2819_;
v___y_2964_ = v_a_2820_;
v___y_2965_ = v_a_2821_;
v___y_2966_ = v_a_2822_;
v___y_2967_ = v_a_2823_;
goto v___jp_2957_;
}
else
{
goto v___jp_3052_;
}
}
else
{
goto v___jp_3052_;
}
v___jp_2989_:
{
lean_object* v___x_2993_; double v___x_2994_; double v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2993_ = lean_io_get_num_heartbeats();
v___x_2994_ = lean_float_of_nat(v___y_2991_);
v___x_2995_ = lean_float_of_nat(v___x_2993_);
v___x_2996_ = lean_box_float(v___x_2994_);
v___x_2997_ = lean_box_float(v___x_2995_);
v___x_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2996_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2999_, 0, v_a_2992_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2852_, v___x_2985_, v___x_2986_, v_options_2849_, v___x_2988_, v___y_2990_, v___f_2984_, v___x_2999_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
return v___x_3000_;
}
v___jp_3001_:
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3005_, 0, v_a_3004_);
v___y_2990_ = v___y_3002_;
v___y_2991_ = v___y_3003_;
v_a_2992_ = v___x_3005_;
goto v___jp_2989_;
}
v___jp_3006_:
{
if (lean_obj_tag(v___y_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
v_a_3010_ = lean_ctor_get(v___y_3009_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___y_3009_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___y_3009_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___y_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
lean_ctor_set_tag(v___x_3012_, 1);
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
v___y_2990_ = v___y_3007_;
v___y_2991_ = v___y_3008_;
v_a_2992_ = v___x_3015_;
goto v___jp_2989_;
}
}
}
else
{
lean_object* v_a_3018_; 
v_a_3018_ = lean_ctor_get(v___y_3009_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___y_3009_, 1);
v___y_3002_ = v___y_3007_;
v___y_3003_ = v___y_3008_;
v_a_3004_ = v_a_3018_;
goto v___jp_3001_;
}
}
v___jp_3019_:
{
lean_object* v___x_3023_; double v___x_3024_; double v___x_3025_; double v___x_3026_; double v___x_3027_; double v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3023_ = lean_io_mono_nanos_now();
v___x_3024_ = lean_float_of_nat(v___y_3020_);
v___x_3025_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__4);
v___x_3026_ = lean_float_div(v___x_3024_, v___x_3025_);
v___x_3027_ = lean_float_of_nat(v___x_3023_);
v___x_3028_ = lean_float_div(v___x_3027_, v___x_3025_);
v___x_3029_ = lean_box_float(v___x_3026_);
v___x_3030_ = lean_box_float(v___x_3028_);
v___x_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v_a_3022_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3(v_cls_2852_, v___x_2985_, v___x_2986_, v_options_2849_, v___x_2988_, v___y_3021_, v___f_2984_, v___x_3032_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
return v___x_3033_;
}
v___jp_3034_:
{
lean_object* v___x_3038_; 
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v_a_3037_);
v___y_3020_ = v___y_3035_;
v___y_3021_ = v___y_3036_;
v_a_3022_ = v___x_3038_;
goto v___jp_3019_;
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
v___y_3020_ = v___y_3040_;
v___y_3021_ = v___y_3041_;
v_a_3022_ = v___x_3048_;
goto v___jp_3019_;
}
}
}
else
{
lean_object* v_a_3051_; 
v_a_3051_ = lean_ctor_get(v___y_3042_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___y_3042_, 1);
v___y_3035_ = v___y_3040_;
v___y_3036_ = v___y_3041_;
v_a_3037_ = v_a_3051_;
goto v___jp_3034_;
}
}
v___jp_3052_:
{
lean_object* v___x_3053_; lean_object* v_a_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; 
v___x_3053_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__1___redArg(v_a_2823_);
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref(v___x_3053_);
v___x_3055_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3056_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__2(v_options_2849_, v___x_3055_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v_a_3059_; uint8_t v___x_3060_; 
v___x_3057_ = lean_io_mono_nanos_now();
v___x_3058_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2852_, v_inheritedTraceOptions_2850_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
v___x_3060_ = lean_unbox(v_a_3059_);
lean_dec(v_a_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_box(0);
v___x_3062_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(v_lhs_2813_, v_rhs_2814_, v___x_3056_, v___f_2853_, v_cls_2852_, v_P_2812_, v___x_3061_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
v___y_3040_ = v___x_3057_;
v___y_3041_ = v_a_3054_;
v___y_3042_ = v___x_3062_;
goto v___jp_3039_;
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3063_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2814_);
lean_inc_ref(v_lhs_2813_);
lean_inc_ref(v_P_2812_);
v___x_3064_ = l_Lean_mkAppB(v_P_2812_, v_lhs_2813_, v_rhs_2814_);
v___x_3065_ = l_Lean_indentExpr(v___x_3064_);
v___x_3066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3063_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2852_, v___x_3066_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3069_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3069_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__7(v_lhs_2813_, v_rhs_2814_, v___x_3056_, v___f_2853_, v_cls_2852_, v_P_2812_, v_a_3068_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
v___y_3040_ = v___x_3057_;
v___y_3041_ = v_a_3054_;
v___y_3042_ = v___x_3069_;
goto v___jp_3039_;
}
else
{
lean_object* v_a_3070_; 
lean_dec_ref(v_rhs_2814_);
lean_dec_ref(v_lhs_2813_);
lean_dec_ref(v_P_2812_);
v_a_3070_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3070_);
lean_dec_ref_known(v___x_3067_, 1);
v___y_3035_ = v___x_3057_;
v___y_3036_ = v_a_3054_;
v_a_3037_ = v_a_3070_;
goto v___jp_3034_;
}
}
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v_a_3073_; uint8_t v___x_3074_; 
v___x_3071_ = lean_io_get_num_heartbeats();
v___x_3072_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2852_, v_inheritedTraceOptions_2850_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref(v___x_3072_);
v___x_3074_ = lean_unbox(v_a_3073_);
lean_dec(v_a_3073_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = lean_box(0);
v___x_3076_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2813_, v_rhs_2814_, v___f_2853_, v_cls_2852_, v_P_2812_, v___x_3075_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
v___y_3007_ = v_a_3054_;
v___y_3008_ = v___x_3071_;
v___y_3009_ = v___x_3076_;
goto v___jp_3006_;
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3077_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2814_);
lean_inc_ref(v_lhs_2813_);
lean_inc_ref(v_P_2812_);
v___x_3078_ = l_Lean_mkAppB(v_P_2812_, v_lhs_2813_, v_rhs_2814_);
v___x_3079_ = l_Lean_indentExpr(v___x_3078_);
v___x_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3077_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2852_, v___x_3080_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3083_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___x_3081_, 1);
v___x_3083_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6(v_lhs_2813_, v_rhs_2814_, v___f_2853_, v_cls_2852_, v_P_2812_, v_a_3082_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
v___y_3007_ = v_a_3054_;
v___y_3008_ = v___x_3071_;
v___y_3009_ = v___x_3083_;
goto v___jp_3006_;
}
else
{
lean_object* v_a_3084_; 
lean_dec_ref(v_rhs_2814_);
lean_dec_ref(v_lhs_2813_);
lean_dec_ref(v_P_2812_);
v_a_3084_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3081_, 1);
v___y_3002_ = v_a_3054_;
v___y_3003_ = v___x_3071_;
v_a_3004_ = v_a_3084_;
goto v___jp_3001_;
}
}
}
}
}
v___jp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2827_, 0, v___y_2826_);
lean_ctor_set_uint8(v___x_2827_, 1, v___y_2826_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
v___jp_2829_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
return v___x_2831_;
}
v___jp_2832_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
return v___x_2834_;
}
v___jp_2835_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2844_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__8);
v___x_2845_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__9));
v___x_2846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2846_, 0, v___y_2837_);
lean_ctor_set(v___x_2846_, 1, v___x_2844_);
lean_ctor_set(v___x_2846_, 2, v___x_2845_);
v___x_2847_ = l_Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_run_x27___redArg(v___y_2836_, v___x_2846_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
return v___x_2847_;
}
v___jp_2854_:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_lhs_2813_);
if (lean_obj_tag(v___x_2864_) == 1)
{
lean_object* v_val_2865_; lean_object* v___x_2866_; 
v_val_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_val_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_ofApp2_x3f(v_rhs_2814_);
if (lean_obj_tag(v___x_2866_) == 1)
{
lean_object* v_val_2867_; uint8_t v___x_2868_; 
v_val_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_val_2867_);
lean_dec_ref_known(v___x_2866_, 1);
v___x_2868_ = lean_expr_eqv(v_val_2865_, v_val_2867_);
if (v___x_2868_ == 0)
{
lean_object* v_toCold_2869_; lean_object* v_inheritedTraceOptions_2870_; lean_object* v___x_2871_; lean_object* v_a_2872_; uint8_t v___x_2873_; 
lean_dec_ref(v_P_2812_);
v_toCold_2869_ = lean_ctor_get(v___y_2862_, 0);
v_inheritedTraceOptions_2870_ = lean_ctor_get(v_toCold_2869_, 11);
v___x_2871_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2852_, v_inheritedTraceOptions_2870_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref(v___x_2871_);
v___x_2873_ = lean_unbox(v_a_2872_);
lean_dec(v_a_2872_);
if (v___x_2873_ == 0)
{
lean_dec(v_val_2867_);
lean_dec(v_val_2865_);
lean_dec_ref(v_rhs_2814_);
lean_dec_ref(v_lhs_2813_);
v___y_2826_ = v___x_2868_;
goto v___jp_2825_;
}
else
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2874_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__2);
v___x_2875_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2865_);
v___x_2876_ = l_Lean_MessageData_ofExpr(v___x_2875_);
v___x_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2874_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__4);
v___x_2879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = l_Lean_indentExpr(v_lhs_2813_);
v___x_2881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__6);
v___x_2883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2867_);
v___x_2885_ = l_Lean_MessageData_ofExpr(v___x_2884_);
v___x_2886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2883_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
v___x_2887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v___x_2878_);
v___x_2888_ = l_Lean_indentExpr(v_rhs_2814_);
v___x_2889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2852_, v___x_2889_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_dec_ref_known(v___x_2890_, 1);
v___y_2826_ = v___x_2868_;
goto v___jp_2825_;
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
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
}
else
{
lean_object* v_toCold_2899_; lean_object* v_options_2900_; lean_object* v_inheritedTraceOptions_2901_; uint8_t v_hasTrace_2902_; uint8_t v___x_2903_; lean_object* v___x_2904_; lean_object* v___f_2905_; 
lean_dec(v_val_2867_);
v_toCold_2899_ = lean_ctor_get(v___y_2862_, 0);
v_options_2900_ = lean_ctor_get(v_toCold_2899_, 2);
v_inheritedTraceOptions_2901_ = lean_ctor_get(v_toCold_2899_, 11);
v_hasTrace_2902_ = lean_ctor_get_uint8(v_options_2900_, sizeof(void*)*1);
v___x_2903_ = 0;
v___x_2904_ = lean_box(v___x_2903_);
lean_inc(v_val_2865_);
v___f_2905_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__2___boxed), 13, 5);
lean_closure_set(v___f_2905_, 0, v_val_2865_);
lean_closure_set(v___f_2905_, 1, v_lhs_2813_);
lean_closure_set(v___f_2905_, 2, v_rhs_2814_);
lean_closure_set(v___f_2905_, 3, v_P_2812_);
lean_closure_set(v___f_2905_, 4, v___x_2904_);
if (v_hasTrace_2902_ == 0)
{
v___y_2836_ = v___f_2905_;
v___y_2837_ = v_val_2865_;
v___y_2838_ = v___y_2858_;
v___y_2839_ = v___y_2859_;
v___y_2840_ = v___y_2860_;
v___y_2841_ = v___y_2861_;
v___y_2842_ = v___y_2862_;
v___y_2843_ = v___y_2863_;
goto v___jp_2835_;
}
else
{
lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2906_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_2907_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2901_, v_options_2900_, v___x_2906_);
if (v___x_2907_ == 0)
{
v___y_2836_ = v___f_2905_;
v___y_2837_ = v_val_2865_;
v___y_2838_ = v___y_2858_;
v___y_2839_ = v___y_2859_;
v___y_2840_ = v___y_2860_;
v___y_2841_ = v___y_2861_;
v___y_2842_ = v___y_2862_;
v___y_2843_ = v___y_2863_;
goto v___jp_2835_;
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2908_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__11);
lean_inc(v_val_2865_);
v___x_2909_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Op_toExpr(v_val_2865_);
v___x_2910_ = l_Lean_MessageData_ofExpr(v___x_2909_);
v___x_2911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2908_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__13);
v___x_2913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2911_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2852_, v___x_2913_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_dec_ref_known(v___x_2914_, 1);
v___y_2836_ = v___f_2905_;
v___y_2837_ = v_val_2865_;
v___y_2838_ = v___y_2858_;
v___y_2839_ = v___y_2859_;
v___y_2840_ = v___y_2860_;
v___y_2841_ = v___y_2861_;
v___y_2842_ = v___y_2862_;
v___y_2843_ = v___y_2863_;
goto v___jp_2835_;
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec_ref(v___f_2905_);
lean_dec(v_val_2865_);
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
else
{
lean_object* v_toCold_2923_; lean_object* v_inheritedTraceOptions_2924_; lean_object* v___x_2925_; lean_object* v_a_2926_; uint8_t v___x_2927_; 
lean_dec(v___x_2866_);
lean_dec(v_val_2865_);
lean_dec_ref(v_lhs_2813_);
lean_dec_ref(v_P_2812_);
v_toCold_2923_ = lean_ctor_get(v___y_2862_, 0);
v_inheritedTraceOptions_2924_ = lean_ctor_get(v_toCold_2923_, 11);
v___x_2925_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2852_, v_inheritedTraceOptions_2924_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref(v___x_2925_);
v___x_2927_ = lean_unbox(v_a_2926_);
lean_dec(v_a_2926_);
if (v___x_2927_ == 0)
{
lean_dec_ref(v_rhs_2814_);
goto v___jp_2832_;
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2928_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2929_ = l_Lean_indentExpr(v_rhs_2814_);
v___x_2930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2928_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___x_2931_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2852_, v___x_2930_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_dec_ref_known(v___x_2931_, 1);
goto v___jp_2832_;
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2931_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_2940_; lean_object* v_inheritedTraceOptions_2941_; lean_object* v___x_2942_; lean_object* v_a_2943_; uint8_t v___x_2944_; 
lean_dec(v___x_2864_);
lean_dec_ref(v_rhs_2814_);
lean_dec_ref(v_P_2812_);
v_toCold_2940_ = lean_ctor_get(v___y_2862_, 0);
v_inheritedTraceOptions_2941_ = lean_ctor_get(v_toCold_2940_, 11);
v___x_2942_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__0(v_cls_2852_, v_inheritedTraceOptions_2941_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref(v___x_2942_);
v___x_2944_ = lean_unbox(v_a_2943_);
lean_dec(v_a_2943_);
if (v___x_2944_ == 0)
{
lean_dec_ref(v_lhs_2813_);
goto v___jp_2829_;
}
else
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2945_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__15);
v___x_2946_ = l_Lean_indentExpr(v_lhs_2813_);
v___x_2947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2945_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2852_, v___x_2947_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_dec_ref_known(v___x_2948_, 1);
goto v___jp_2829_;
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
}
v___jp_2957_:
{
if (v_____do__lift_2958_ == 0)
{
v___y_2855_ = v___y_2959_;
v___y_2856_ = v___y_2960_;
v___y_2857_ = v___y_2961_;
v___y_2858_ = v___y_2962_;
v___y_2859_ = v___y_2963_;
v___y_2860_ = v___y_2964_;
v___y_2861_ = v___y_2965_;
v___y_2862_ = v___y_2966_;
v___y_2863_ = v___y_2967_;
goto v___jp_2854_;
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2968_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___closed__2);
lean_inc_ref(v_rhs_2814_);
lean_inc_ref(v_lhs_2813_);
lean_inc_ref(v_P_2812_);
v___x_2969_ = l_Lean_mkAppB(v_P_2812_, v_lhs_2813_, v_rhs_2814_);
v___x_2970_ = l_Lean_indentExpr(v___x_2969_);
v___x_2971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2968_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_2852_, v___x_2971_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_dec_ref_known(v___x_2972_, 1);
v___y_2855_ = v___y_2959_;
v___y_2856_ = v___y_2960_;
v___y_2857_ = v___y_2961_;
v___y_2858_ = v___y_2962_;
v___y_2859_ = v___y_2963_;
v___y_2860_ = v___y_2964_;
v___y_2861_ = v___y_2965_;
v___y_2862_ = v___y_2966_;
v___y_2863_ = v___y_2967_;
goto v___jp_2854_;
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v_rhs_2814_);
lean_dec_ref(v_lhs_2813_);
lean_dec_ref(v_P_2812_);
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___boxed(lean_object* v_P_3090_, lean_object* v_lhs_3091_, lean_object* v_rhs_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v_P_3090_, v_lhs_3091_, v_rhs_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(lean_object* v_cls_3104_, lean_object* v_msg_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v_cls_3104_, v_msg_3105_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___boxed(lean_object* v_cls_3117_, lean_object* v_msg_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0(v_cls_3117_, v_msg_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(lean_object* v_00_u03b1_3130_, lean_object* v_x_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___redArg(v_x_3131_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4___boxed(lean_object* v_00_u03b1_3143_, lean_object* v_x_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__4(v_00_u03b1_3143_, v_x_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(lean_object* v_oldTraces_3156_, lean_object* v_data_3157_, lean_object* v_ref_3158_, lean_object* v_msg_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___redArg(v_oldTraces_3156_, v_data_3157_, v_ref_3158_, v_msg_3159_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3___boxed(lean_object* v_oldTraces_3171_, lean_object* v_data_3172_, lean_object* v_ref_3173_, lean_object* v_msg_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__3_spec__3(v_oldTraces_3171_, v_data_3172_, v_ref_3173_, v_msg_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(lean_object* v_x_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0___boxed(lean_object* v_x_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v_x_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(lean_object* v_arg_3211_, lean_object* v___x_3212_, lean_object* v_arg_3213_, lean_object* v_arg_3214_, lean_object* v_arg_3215_, lean_object* v_____r_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___x_3227_; 
lean_inc_ref(v_arg_3211_);
v___x_3227_ = l_Lean_Meta_getDecLevel(v_arg_3211_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___x_3227_, 1);
v___x_3229_ = lean_box(0);
v___x_3230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_a_3228_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = l_Lean_Expr_const___override(v___x_3212_, v___x_3230_);
v___x_3232_ = l_Lean_mkAppB(v___x_3231_, v_arg_3211_, v_arg_3213_);
v___x_3233_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3232_, v_arg_3214_, v_arg_3215_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
return v___x_3233_;
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v_arg_3215_);
lean_dec_ref(v_arg_3214_);
lean_dec_ref(v_arg_3213_);
lean_dec(v___x_3212_);
lean_dec_ref(v_arg_3211_);
v_a_3234_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3227_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3227_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1___boxed(lean_object* v_arg_3242_, lean_object* v___x_3243_, lean_object* v_arg_3244_, lean_object* v_arg_3245_, lean_object* v_arg_3246_, lean_object* v_____r_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3242_, v___x_3243_, v_arg_3244_, v_arg_3245_, v_arg_3246_, v_____r_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(lean_object* v_arg_3262_, lean_object* v_arg_3263_, lean_object* v_arg_3264_, lean_object* v_____r_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v___x_3276_; 
lean_inc_ref(v_arg_3262_);
v___x_3276_ = l_Lean_Meta_getLevel(v_arg_3262_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v___x_3278_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3279_ = lean_box(0);
v___x_3280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3280_, 0, v_a_3277_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = l_Lean_Expr_const___override(v___x_3278_, v___x_3280_);
v___x_3282_ = l_Lean_Expr_app___override(v___x_3281_, v_arg_3262_);
v___x_3283_ = l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing(v___x_3282_, v_arg_3263_, v_arg_3264_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
return v___x_3283_;
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec_ref(v_arg_3264_);
lean_dec_ref(v_arg_3263_);
lean_dec_ref(v_arg_3262_);
v_a_3284_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3276_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3276_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___boxed(lean_object* v_arg_3292_, lean_object* v_arg_3293_, lean_object* v_arg_3294_, lean_object* v_____r_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3292_, v_arg_3293_, v_arg_3294_, v_____r_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
return v_res_3306_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__3));
v___x_3314_ = l_Lean_stringToMessageData(v___x_3313_);
return v___x_3314_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = l_Lean_checkEmoji;
v___x_3316_ = l_Lean_stringToMessageData(v___x_3315_);
return v___x_3316_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6(void){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__5);
v___x_3318_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__4);
v___x_3319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
lean_ctor_set(v___x_3319_, 1, v___x_3317_);
return v___x_3319_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__7));
v___x_3322_ = l_Lean_stringToMessageData(v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__8);
v___x_3324_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v___x_3323_);
return v___x_3325_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11(void){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__10));
v___x_3328_ = l_Lean_stringToMessageData(v___x_3327_);
return v___x_3328_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__12(void){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3329_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__11);
v___x_3330_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__6);
v___x_3331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
lean_ctor_set(v___x_3331_, 1, v___x_3329_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(lean_object* v_e_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v___y_3344_; lean_object* v___x_3376_; 
v___x_3376_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3332_, v_a_3339_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
v___x_3378_ = l_Lean_Expr_cleanupAnnotations(v_a_3377_);
lean_dec(v_a_3377_);
v___x_3379_ = l_Lean_Expr_isApp(v___x_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec_ref(v___x_3378_);
v___x_3380_ = lean_box(0);
v___x_3381_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3380_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
v___y_3344_ = v___x_3381_;
goto v___jp_3343_;
}
else
{
lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3378_);
v___x_3383_ = l_Lean_Expr_isApp(v___x_3382_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_dec_ref(v___x_3382_);
lean_dec_ref(v___x_3378_);
v___x_3384_ = lean_box(0);
v___x_3385_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3384_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
v___y_3344_ = v___x_3385_;
goto v___jp_3343_;
}
else
{
lean_object* v___x_3386_; uint8_t v___x_3387_; 
v___x_3386_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3382_);
v___x_3387_ = l_Lean_Expr_isApp(v___x_3386_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
lean_dec_ref(v___x_3386_);
lean_dec_ref(v___x_3382_);
lean_dec_ref(v___x_3378_);
v___x_3388_ = lean_box(0);
v___x_3389_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3388_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
v___y_3344_ = v___x_3389_;
goto v___jp_3343_;
}
else
{
lean_object* v_arg_3390_; lean_object* v_arg_3391_; lean_object* v_arg_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v_arg_3390_ = lean_ctor_get(v___x_3378_, 1);
lean_inc_ref(v_arg_3390_);
lean_dec_ref(v___x_3378_);
v_arg_3391_ = lean_ctor_get(v___x_3382_, 1);
lean_inc_ref(v_arg_3391_);
lean_dec_ref(v___x_3382_);
v_arg_3392_ = lean_ctor_get(v___x_3386_, 1);
lean_inc_ref(v_arg_3392_);
v___x_3393_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3386_);
lean_dec_ref(v___x_3386_);
v___x_3394_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2___closed__1));
v___x_3395_ = l_Lean_Expr_isConstOf(v___x_3393_, v___x_3394_);
if (v___x_3395_ == 0)
{
uint8_t v___x_3396_; 
v___x_3396_ = l_Lean_Expr_isApp(v___x_3393_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
lean_dec_ref(v___x_3393_);
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_arg_3391_);
lean_dec_ref(v_arg_3390_);
v___x_3397_ = lean_box(0);
v___x_3398_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3397_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
v___y_3344_ = v___x_3398_;
goto v___jp_3343_;
}
else
{
lean_object* v___x_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v___x_3399_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3393_);
v___x_3400_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__2));
v___x_3401_ = l_Lean_Expr_isConstOf(v___x_3399_, v___x_3400_);
lean_dec_ref(v___x_3399_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec_ref(v___x_3393_);
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_arg_3391_);
lean_dec_ref(v_arg_3390_);
v___x_3402_ = lean_box(0);
v___x_3403_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__0(v___x_3402_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
v___y_3344_ = v___x_3403_;
goto v___jp_3343_;
}
else
{
lean_object* v_toCold_3404_; lean_object* v_options_3405_; lean_object* v_arg_3406_; lean_object* v_inheritedTraceOptions_3407_; uint8_t v_hasTrace_3408_; 
v_toCold_3404_ = lean_ctor_get(v_a_3340_, 0);
v_options_3405_ = lean_ctor_get(v_toCold_3404_, 2);
v_arg_3406_ = lean_ctor_get(v___x_3393_, 1);
lean_inc_ref(v_arg_3406_);
lean_dec_ref(v___x_3393_);
v_inheritedTraceOptions_3407_ = lean_ctor_get(v_toCold_3404_, 11);
v_hasTrace_3408_ = lean_ctor_get_uint8(v_options_3405_, sizeof(void*)*1);
if (v_hasTrace_3408_ == 0)
{
goto v___jp_3409_;
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3414_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3407_, v_options_3405_, v___x_3413_);
if (v___x_3414_ == 0)
{
goto v___jp_3409_;
}
else
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__9);
v___x_3416_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3412_, v___x_3415_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3418_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref_known(v___x_3416_, 1);
v___x_3418_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3406_, v___x_3400_, v_arg_3392_, v_arg_3391_, v_arg_3390_, v_a_3417_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
v___y_3344_ = v___x_3418_;
goto v___jp_3343_;
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec_ref(v_arg_3406_);
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_arg_3391_);
lean_dec_ref(v_arg_3390_);
v_a_3419_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3416_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3416_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
v___jp_3409_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = lean_box(0);
v___x_3411_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__1(v_arg_3406_, v___x_3400_, v_arg_3392_, v_arg_3391_, v_arg_3390_, v___x_3410_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
v___y_3344_ = v___x_3411_;
goto v___jp_3343_;
}
}
}
}
else
{
lean_object* v_toCold_3427_; lean_object* v_options_3428_; lean_object* v_inheritedTraceOptions_3429_; uint8_t v_hasTrace_3430_; 
lean_dec_ref(v___x_3393_);
v_toCold_3427_ = lean_ctor_get(v_a_3340_, 0);
v_options_3428_ = lean_ctor_get(v_toCold_3427_, 2);
v_inheritedTraceOptions_3429_ = lean_ctor_get(v_toCold_3427_, 11);
v_hasTrace_3430_ = lean_ctor_get_uint8(v_options_3428_, sizeof(void*)*1);
if (v_hasTrace_3430_ == 0)
{
goto v___jp_3431_;
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v___x_3434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3436_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3429_, v_options_3428_, v___x_3435_);
if (v___x_3436_ == 0)
{
goto v___jp_3431_;
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___closed__12);
v___x_3438_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing_spec__0___redArg(v___x_3434_, v___x_3437_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3438_, 1);
v___x_3440_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3392_, v_arg_3391_, v_arg_3390_, v_a_3439_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
v___y_3344_ = v___x_3440_;
goto v___jp_3343_;
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_arg_3391_);
lean_dec_ref(v_arg_3390_);
v_a_3441_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3438_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3438_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
v___jp_3431_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3432_ = lean_box(0);
v___x_3433_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___lam__2(v_arg_3392_, v_arg_3391_, v_arg_3390_, v___x_3432_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
v___y_3344_ = v___x_3433_;
goto v___jp_3343_;
}
}
}
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
v_a_3449_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3376_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3376_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
v___jp_3343_:
{
if (lean_obj_tag(v___y_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3375_; 
v_a_3345_ = lean_ctor_get(v___y_3344_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___y_3344_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3347_ = v___y_3344_;
v_isShared_3348_ = v_isSharedCheck_3375_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___y_3344_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3375_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
if (lean_obj_tag(v_a_3345_) == 0)
{
uint8_t v_contextDependent_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3360_; 
v_contextDependent_3349_ = lean_ctor_get_uint8(v_a_3345_, 1);
v_isSharedCheck_3360_ = !lean_is_exclusive(v_a_3345_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3351_ = v_a_3345_;
v_isShared_3352_ = v_isSharedCheck_3360_;
goto v_resetjp_3350_;
}
else
{
lean_dec(v_a_3345_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3360_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
uint8_t v___x_3353_; lean_object* v___x_3355_; 
v___x_3353_ = 1;
if (v_isShared_3352_ == 0)
{
v___x_3355_ = v___x_3351_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_3359_, 1, v_contextDependent_3349_);
v___x_3355_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
lean_object* v___x_3357_; 
lean_ctor_set_uint8(v___x_3355_, 0, v___x_3353_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3355_);
v___x_3357_ = v___x_3347_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3355_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
else
{
lean_object* v_e_x27_3361_; lean_object* v_proof_3362_; uint8_t v_contextDependent_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3374_; 
v_e_x27_3361_ = lean_ctor_get(v_a_3345_, 0);
v_proof_3362_ = lean_ctor_get(v_a_3345_, 1);
v_contextDependent_3363_ = lean_ctor_get_uint8(v_a_3345_, sizeof(void*)*2 + 1);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_a_3345_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3365_ = v_a_3345_;
v_isShared_3366_ = v_isSharedCheck_3374_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_proof_3362_);
lean_inc(v_e_x27_3361_);
lean_dec(v_a_3345_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3374_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
uint8_t v___x_3367_; lean_object* v___x_3369_; 
v___x_3367_ = 1;
if (v_isShared_3366_ == 0)
{
v___x_3369_ = v___x_3365_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_e_x27_3361_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_proof_3362_);
lean_ctor_set_uint8(v_reuseFailAlloc_3373_, sizeof(void*)*2 + 1, v_contextDependent_3363_);
v___x_3369_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3371_; 
lean_ctor_set_uint8(v___x_3369_, sizeof(void*)*2, v___x_3367_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3369_);
v___x_3371_ = v___x_3347_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
}
else
{
return v___y_3344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed(lean_object* v_e_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost(v_e_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(lean_object* v_x_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v___x_3482_; 
lean_inc(v___y_3476_);
lean_inc_ref(v___y_3475_);
lean_inc(v___y_3474_);
lean_inc_ref(v___y_3473_);
lean_inc(v___y_3472_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
v___x_3482_ = lean_apply_12(v_x_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, lean_box(0));
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed(lean_object* v_x_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0(v_x_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(lean_object* v_mvarId_3497_, lean_object* v_x_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v___f_3511_; lean_object* v___x_3512_; 
lean_inc(v___y_3505_);
lean_inc_ref(v___y_3504_);
lean_inc(v___y_3503_);
lean_inc_ref(v___y_3502_);
lean_inc(v___y_3501_);
lean_inc(v___y_3500_);
lean_inc_ref(v___y_3499_);
v___f_3511_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_3511_, 0, v_x_3498_);
lean_closure_set(v___f_3511_, 1, v___y_3499_);
lean_closure_set(v___f_3511_, 2, v___y_3500_);
lean_closure_set(v___f_3511_, 3, v___y_3501_);
lean_closure_set(v___f_3511_, 4, v___y_3502_);
lean_closure_set(v___f_3511_, 5, v___y_3503_);
lean_closure_set(v___f_3511_, 6, v___y_3504_);
lean_closure_set(v___f_3511_, 7, v___y_3505_);
v___x_3512_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3497_, v___f_3511_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3512_) == 0)
{
return v___x_3512_;
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg___boxed(lean_object* v_mvarId_3521_, lean_object* v_x_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3521_, v_x_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(lean_object* v_00_u03b1_3536_, lean_object* v_mvarId_3537_, lean_object* v_x_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v_mvarId_3537_, v_x_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___boxed(lean_object* v_00_u03b1_3552_, lean_object* v_mvarId_3553_, lean_object* v_x_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2(v_00_u03b1_3552_, v_mvarId_3553_, v_x_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(lean_object* v_x_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_canonicalizeWithSharing___lam__6___closed__0));
v___x_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0___boxed(lean_object* v_x_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__0(v_x_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v_x_3581_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(lean_object* v_snd_3593_, lean_object* v_a_3594_, lean_object* v___x_3595_, lean_object* v_____r_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3609_ = lean_array_push(v_snd_3593_, v_a_3594_);
v___x_3610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3595_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
v___x_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed(lean_object* v_snd_3613_, lean_object* v_a_3614_, lean_object* v___x_3615_, lean_object* v_____r_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3613_, v_a_3614_, v___x_3615_, v_____r_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(lean_object* v_cls_3630_, lean_object* v_msg_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v_ref_3637_; lean_object* v___x_3638_; lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3684_; 
v_ref_3637_ = lean_ctor_get(v___y_3634_, 2);
v___x_3638_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_varToExpr_spec__1_spec__1(v_msg_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3641_ = v___x_3638_;
v_isShared_3642_ = v_isSharedCheck_3684_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3684_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; lean_object* v_traceState_3644_; lean_object* v_env_3645_; lean_object* v_nextMacroScope_3646_; lean_object* v_ngen_3647_; lean_object* v_auxDeclNGen_3648_; lean_object* v_cache_3649_; lean_object* v_recordedDeps_3650_; lean_object* v_messages_3651_; lean_object* v_infoState_3652_; lean_object* v_snapshotTasks_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3683_; 
v___x_3643_ = lean_st_ref_take(v___y_3635_);
v_traceState_3644_ = lean_ctor_get(v___x_3643_, 4);
v_env_3645_ = lean_ctor_get(v___x_3643_, 0);
v_nextMacroScope_3646_ = lean_ctor_get(v___x_3643_, 1);
v_ngen_3647_ = lean_ctor_get(v___x_3643_, 2);
v_auxDeclNGen_3648_ = lean_ctor_get(v___x_3643_, 3);
v_cache_3649_ = lean_ctor_get(v___x_3643_, 5);
v_recordedDeps_3650_ = lean_ctor_get(v___x_3643_, 6);
v_messages_3651_ = lean_ctor_get(v___x_3643_, 7);
v_infoState_3652_ = lean_ctor_get(v___x_3643_, 8);
v_snapshotTasks_3653_ = lean_ctor_get(v___x_3643_, 9);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3655_ = v___x_3643_;
v_isShared_3656_ = v_isSharedCheck_3683_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_snapshotTasks_3653_);
lean_inc(v_infoState_3652_);
lean_inc(v_messages_3651_);
lean_inc(v_recordedDeps_3650_);
lean_inc(v_cache_3649_);
lean_inc(v_traceState_3644_);
lean_inc(v_auxDeclNGen_3648_);
lean_inc(v_ngen_3647_);
lean_inc(v_nextMacroScope_3646_);
lean_inc(v_env_3645_);
lean_dec(v___x_3643_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3683_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
uint64_t v_tid_3657_; lean_object* v_traces_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3682_; 
v_tid_3657_ = lean_ctor_get_uint64(v_traceState_3644_, sizeof(void*)*1);
v_traces_3658_ = lean_ctor_get(v_traceState_3644_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v_traceState_3644_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3660_ = v_traceState_3644_;
v_isShared_3661_ = v_isSharedCheck_3682_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_traces_3658_);
lean_dec(v_traceState_3644_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3682_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; double v___x_3664_; uint8_t v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3673_; 
v___x_3662_ = lean_box(0);
v___x_3663_ = lean_box(0);
v___x_3664_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__0);
v___x_3665_ = 0;
v___x_3666_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__1));
v___x_3667_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3667_, 0, v_cls_3630_);
lean_ctor_set(v___x_3667_, 1, v___x_3663_);
lean_ctor_set(v___x_3667_, 2, v___x_3666_);
lean_ctor_set_float(v___x_3667_, sizeof(void*)*3, v___x_3664_);
lean_ctor_set_float(v___x_3667_, sizeof(void*)*3 + 8, v___x_3664_);
lean_ctor_set_uint8(v___x_3667_, sizeof(void*)*3 + 16, v___x_3665_);
v___x_3668_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go_spec__0___redArg___closed__2));
v___x_3669_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3667_);
lean_ctor_set(v___x_3669_, 1, v_a_3639_);
lean_ctor_set(v___x_3669_, 2, v___x_3668_);
lean_inc(v_ref_3637_);
v___x_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3670_, 0, v_ref_3637_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
v___x_3671_ = l_Lean_PersistentArray_push___redArg(v_traces_3658_, v___x_3670_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3671_);
v___x_3673_ = v___x_3660_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3671_);
lean_ctor_set_uint64(v_reuseFailAlloc_3681_, sizeof(void*)*1, v_tid_3657_);
v___x_3673_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
lean_object* v___x_3675_; 
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 4, v___x_3673_);
v___x_3675_ = v___x_3655_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_env_3645_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_nextMacroScope_3646_);
lean_ctor_set(v_reuseFailAlloc_3680_, 2, v_ngen_3647_);
lean_ctor_set(v_reuseFailAlloc_3680_, 3, v_auxDeclNGen_3648_);
lean_ctor_set(v_reuseFailAlloc_3680_, 4, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3680_, 5, v_cache_3649_);
lean_ctor_set(v_reuseFailAlloc_3680_, 6, v_recordedDeps_3650_);
lean_ctor_set(v_reuseFailAlloc_3680_, 7, v_messages_3651_);
lean_ctor_set(v_reuseFailAlloc_3680_, 8, v_infoState_3652_);
lean_ctor_set(v_reuseFailAlloc_3680_, 9, v_snapshotTasks_3653_);
v___x_3675_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3676_; lean_object* v___x_3678_; 
v___x_3676_ = lean_st_ref_put(v___y_3635_, v___x_3675_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3662_);
v___x_3678_ = v___x_3641_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3662_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg___boxed(lean_object* v_cls_3685_, lean_object* v_msg_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_3685_, v_msg_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(uint8_t v___x_3693_, lean_object* v___f_3694_, lean_object* v_____r_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v___x_3708_; lean_object* v_caches_3709_; lean_object* v_typeAnalysis_3710_; lean_object* v_target_3711_; lean_object* v_hypotheses_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3722_; 
v___x_3708_ = lean_st_ref_take(v___y_3697_);
v_caches_3709_ = lean_ctor_get(v___x_3708_, 0);
v_typeAnalysis_3710_ = lean_ctor_get(v___x_3708_, 1);
v_target_3711_ = lean_ctor_get(v___x_3708_, 2);
v_hypotheses_3712_ = lean_ctor_get(v___x_3708_, 3);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3714_ = v___x_3708_;
v_isShared_3715_ = v_isSharedCheck_3722_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_hypotheses_3712_);
lean_inc(v_target_3711_);
lean_inc(v_typeAnalysis_3710_);
lean_inc(v_caches_3709_);
lean_dec(v___x_3708_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3722_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3716_; lean_object* v___x_3718_; 
v___x_3716_ = lean_box(0);
if (v_isShared_3715_ == 0)
{
v___x_3718_ = v___x_3714_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_caches_3709_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_typeAnalysis_3710_);
lean_ctor_set(v_reuseFailAlloc_3721_, 2, v_target_3711_);
lean_ctor_set(v_reuseFailAlloc_3721_, 3, v_hypotheses_3712_);
v___x_3718_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
lean_ctor_set_uint8(v___x_3718_, sizeof(void*)*4, v___x_3693_);
v___x_3719_ = lean_st_ref_put(v___y_3697_, v___x_3718_);
lean_inc(v___y_3706_);
lean_inc_ref(v___y_3705_);
lean_inc(v___y_3704_);
lean_inc_ref(v___y_3703_);
lean_inc(v___y_3702_);
lean_inc_ref(v___y_3701_);
lean_inc(v___y_3700_);
lean_inc_ref(v___y_3699_);
lean_inc(v___y_3698_);
lean_inc(v___y_3697_);
lean_inc_ref(v___y_3696_);
v___x_3720_ = lean_apply_13(v___f_3694_, v___x_3716_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, lean_box(0));
return v___x_3720_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2___boxed(lean_object* v___x_3723_, lean_object* v___f_3724_, lean_object* v_____r_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
uint8_t v___x_10093__boxed_3738_; lean_object* v_res_3739_; 
v___x_10093__boxed_3738_ = lean_unbox(v___x_3723_);
v_res_3739_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_10093__boxed_3738_, v___f_3724_, v_____r_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
return v_res_3739_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3741_; lean_object* v___f_3742_; lean_object* v_methods_3743_; 
v___x_3741_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNfpost___boxed), 11, 0);
v___f_3742_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__0));
v_methods_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_methods_3743_, 0, v___f_3742_);
lean_ctor_set(v_methods_3743_, 1, v___x_3741_);
return v_methods_3743_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3745_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__2));
v___x_3746_ = l_Lean_stringToMessageData(v___x_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(lean_object* v_upperBound_3747_, lean_object* v___x_3748_, lean_object* v_config_3749_, lean_object* v_a_3750_, lean_object* v_b_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v___y_3765_; uint8_t v___x_3787_; 
v___x_3787_ = lean_nat_dec_lt(v_a_3750_, v_upperBound_3747_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; 
lean_dec(v_a_3750_);
lean_dec_ref(v_config_3749_);
v___x_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3788_, 0, v_b_3751_);
return v___x_3788_;
}
else
{
lean_object* v_snd_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3863_; 
v_snd_3789_ = lean_ctor_get(v_b_3751_, 1);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_b_3751_);
if (v_isSharedCheck_3863_ == 0)
{
lean_object* v_unused_3864_; 
v_unused_3864_ = lean_ctor_get(v_b_3751_, 0);
lean_dec(v_unused_3864_);
v___x_3791_ = v_b_3751_;
v_isShared_3792_ = v_isSharedCheck_3863_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_snd_3789_);
lean_dec(v_b_3751_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3863_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
uint8_t v___x_3793_; lean_object* v_methods_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3793_ = 1;
v_methods_3794_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__1);
v___x_3795_ = lean_box(0);
v___x_3796_ = lean_array_fget_borrowed(v___x_3748_, v_a_3750_);
lean_inc(v___x_3796_);
lean_inc_ref(v_config_3749_);
v___x_3797_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v___x_3793_, v_methods_3794_, v_config_3749_, v___x_3796_, v___y_3753_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v_type_3799_; lean_object* v_value_3800_; uint8_t v___x_3801_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v_type_3799_ = lean_ctor_get(v_a_3798_, 1);
v_value_3800_ = lean_ctor_get(v_a_3798_, 2);
v___x_3801_ = l_Lean_Expr_isFalse(v_type_3799_);
if (v___x_3801_ == 0)
{
lean_object* v_type_3802_; lean_object* v___f_3803_; uint8_t v___x_3804_; 
lean_del_object(v___x_3791_);
v_type_3802_ = lean_ctor_get(v___x_3796_, 1);
lean_inc(v_a_3798_);
lean_inc(v_snd_3789_);
v___f_3803_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1___boxed), 16, 3);
lean_closure_set(v___f_3803_, 0, v_snd_3789_);
lean_closure_set(v___f_3803_, 1, v_a_3798_);
lean_closure_set(v___f_3803_, 2, v___x_3795_);
v___x_3804_ = lean_expr_eqv(v_type_3802_, v_type_3799_);
if (v___x_3804_ == 0)
{
lean_object* v_toCold_3805_; lean_object* v_options_3806_; lean_object* v_inheritedTraceOptions_3807_; uint8_t v_hasTrace_3808_; 
lean_inc_ref(v_type_3799_);
lean_dec(v_a_3798_);
lean_dec(v_snd_3789_);
v_toCold_3805_ = lean_ctor_get(v___y_3761_, 0);
v_options_3806_ = lean_ctor_get(v_toCold_3805_, 2);
v_inheritedTraceOptions_3807_ = lean_ctor_get(v_toCold_3805_, 11);
v_hasTrace_3808_ = lean_ctor_get_uint8(v_options_3806_, sizeof(void*)*1);
if (v_hasTrace_3808_ == 0)
{
lean_dec_ref(v_type_3799_);
goto v___jp_3809_;
}
else
{
lean_object* v___x_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__3));
v___x_3813_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_AC_0__Lean_Meta_Tactic_BVDecide_Normalize_VarStateM_computeCoefficients_go___closed__6);
v___x_3814_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3807_, v_options_3806_, v___x_3813_);
if (v___x_3814_ == 0)
{
lean_dec_ref(v_type_3799_);
goto v___jp_3809_;
}
else
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
lean_inc_ref(v_type_3802_);
v___x_3815_ = l_Lean_MessageData_ofExpr(v_type_3802_);
v___x_3816_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___closed__3);
v___x_3817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3815_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = l_Lean_MessageData_ofExpr(v_type_3799_);
v___x_3819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3817_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
v___x_3820_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v___x_3812_, v___x_3819_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; lean_object* v___x_3822_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v___x_3820_, 1);
v___x_3822_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3787_, v___f_3803_, v_a_3821_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
v___y_3765_ = v___x_3822_;
goto v___jp_3764_;
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec_ref(v___f_3803_);
lean_dec(v_a_3750_);
lean_dec_ref(v_config_3749_);
v_a_3823_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3820_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3820_);
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
v___jp_3809_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = lean_box(0);
v___x_3811_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__2(v___x_3787_, v___f_3803_, v___x_3810_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
v___y_3765_ = v___x_3811_;
goto v___jp_3764_;
}
}
else
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
lean_dec_ref(v___f_3803_);
v___x_3831_ = lean_box(0);
v___x_3832_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___lam__1(v_snd_3789_, v_a_3798_, v___x_3795_, v___x_3831_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
v___y_3765_ = v___x_3832_;
goto v___jp_3764_;
}
}
else
{
lean_object* v___x_3833_; 
lean_inc_ref(v_value_3800_);
lean_dec(v_a_3798_);
lean_dec(v_a_3750_);
lean_dec_ref(v_config_3749_);
v___x_3833_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_3800_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3845_; 
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3845_ == 0)
{
lean_object* v_unused_3846_; 
v_unused_3846_ = lean_ctor_get(v___x_3833_, 0);
lean_dec(v_unused_3846_);
v___x_3835_ = v___x_3833_;
v_isShared_3836_ = v_isSharedCheck_3845_;
goto v_resetjp_3834_;
}
else
{
lean_dec(v___x_3833_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3845_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3840_; 
v___x_3837_ = lean_box(v___x_3787_);
v___x_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3838_);
v___x_3840_ = v___x_3791_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3838_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v_snd_3789_);
v___x_3840_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3842_; 
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v___x_3840_);
v___x_3842_ = v___x_3835_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3840_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_del_object(v___x_3791_);
lean_dec(v_snd_3789_);
v_a_3847_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3833_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3833_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_del_object(v___x_3791_);
lean_dec(v_snd_3789_);
lean_dec(v_a_3750_);
lean_dec_ref(v_config_3749_);
v_a_3855_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3797_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3797_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
}
v___jp_3764_:
{
if (lean_obj_tag(v___y_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3778_; 
v_a_3766_ = lean_ctor_get(v___y_3765_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___y_3765_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3768_ = v___y_3765_;
v_isShared_3769_ = v_isSharedCheck_3778_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___y_3765_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3778_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
if (lean_obj_tag(v_a_3766_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3772_; 
lean_dec(v_a_3750_);
lean_dec_ref(v_config_3749_);
v_a_3770_ = lean_ctor_get(v_a_3766_, 0);
lean_inc(v_a_3770_);
lean_dec_ref_known(v_a_3766_, 1);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 0, v_a_3770_);
v___x_3772_ = v___x_3768_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3770_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
lean_del_object(v___x_3768_);
v_a_3774_ = lean_ctor_get(v_a_3766_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v_a_3766_, 1);
v___x_3775_ = lean_unsigned_to_nat(1u);
v___x_3776_ = lean_nat_add(v_a_3750_, v___x_3775_);
lean_dec(v_a_3750_);
v_a_3750_ = v___x_3776_;
v_b_3751_ = v_a_3774_;
goto _start;
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec(v_a_3750_);
lean_dec_ref(v_config_3749_);
v_a_3779_ = lean_ctor_get(v___y_3765_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___y_3765_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___y_3765_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___y_3765_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_3865_ = _args[0];
lean_object* v___x_3866_ = _args[1];
lean_object* v_config_3867_ = _args[2];
lean_object* v_a_3868_ = _args[3];
lean_object* v_b_3869_ = _args[4];
lean_object* v___y_3870_ = _args[5];
lean_object* v___y_3871_ = _args[6];
lean_object* v___y_3872_ = _args[7];
lean_object* v___y_3873_ = _args[8];
lean_object* v___y_3874_ = _args[9];
lean_object* v___y_3875_ = _args[10];
lean_object* v___y_3876_ = _args[11];
lean_object* v___y_3877_ = _args[12];
lean_object* v___y_3878_ = _args[13];
lean_object* v___y_3879_ = _args[14];
lean_object* v___y_3880_ = _args[15];
lean_object* v___y_3881_ = _args[16];
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_3865_, v___x_3866_, v_config_3867_, v_a_3868_, v_b_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec_ref(v___x_3866_);
lean_dec(v_upperBound_3865_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(lean_object* v_config_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v___x_3896_; lean_object* v_hypotheses_3897_; lean_object* v___x_3898_; lean_object* v_newHyps_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3896_ = lean_st_ref_get(v___y_3885_);
v_hypotheses_3897_ = lean_ctor_get(v___x_3896_, 3);
lean_inc_ref(v_hypotheses_3897_);
lean_dec(v___x_3896_);
v___x_3898_ = lean_array_get_size(v_hypotheses_3897_);
v_newHyps_3899_ = lean_mk_empty_array_with_capacity(v___x_3898_);
v___x_3900_ = lean_unsigned_to_nat(0u);
v___x_3901_ = lean_box(0);
v___x_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3901_);
lean_ctor_set(v___x_3902_, 1, v_newHyps_3899_);
v___x_3903_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v___x_3898_, v_hypotheses_3897_, v_config_3883_, v___x_3900_, v___x_3902_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
lean_dec_ref(v_hypotheses_3897_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3933_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3906_ = v___x_3903_;
v_isShared_3907_ = v_isSharedCheck_3933_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3933_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v_fst_3908_; 
v_fst_3908_ = lean_ctor_get(v_a_3904_, 0);
if (lean_obj_tag(v_fst_3908_) == 0)
{
lean_object* v_snd_3909_; lean_object* v___x_3910_; lean_object* v_caches_3911_; lean_object* v_typeAnalysis_3912_; lean_object* v_target_3913_; uint8_t v_didChange_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3927_; 
v_snd_3909_ = lean_ctor_get(v_a_3904_, 1);
lean_inc(v_snd_3909_);
lean_dec(v_a_3904_);
v___x_3910_ = lean_st_ref_take(v___y_3885_);
v_caches_3911_ = lean_ctor_get(v___x_3910_, 0);
v_typeAnalysis_3912_ = lean_ctor_get(v___x_3910_, 1);
v_target_3913_ = lean_ctor_get(v___x_3910_, 2);
v_didChange_3914_ = lean_ctor_get_uint8(v___x_3910_, sizeof(void*)*4);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3927_ == 0)
{
lean_object* v_unused_3928_; 
v_unused_3928_ = lean_ctor_get(v___x_3910_, 3);
lean_dec(v_unused_3928_);
v___x_3916_ = v___x_3910_;
v_isShared_3917_ = v_isSharedCheck_3927_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_target_3913_);
lean_inc(v_typeAnalysis_3912_);
lean_inc(v_caches_3911_);
lean_dec(v___x_3910_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3927_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 3, v_snd_3909_);
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_caches_3911_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_typeAnalysis_3912_);
lean_ctor_set(v_reuseFailAlloc_3926_, 2, v_target_3913_);
lean_ctor_set(v_reuseFailAlloc_3926_, 3, v_snd_3909_);
lean_ctor_set_uint8(v_reuseFailAlloc_3926_, sizeof(void*)*4, v_didChange_3914_);
v___x_3919_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3920_; uint8_t v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3924_; 
v___x_3920_ = lean_st_ref_put(v___y_3885_, v___x_3919_);
v___x_3921_ = 0;
v___x_3922_ = lean_box(v___x_3921_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v___x_3922_);
v___x_3924_ = v___x_3906_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3922_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
else
{
lean_object* v_val_3929_; lean_object* v___x_3931_; 
lean_inc_ref(v_fst_3908_);
lean_dec(v_a_3904_);
v_val_3929_ = lean_ctor_get(v_fst_3908_, 0);
lean_inc(v_val_3929_);
lean_dec_ref_known(v_fst_3908_, 1);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v_val_3929_);
v___x_3931_ = v___x_3906_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_val_3929_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
v_a_3934_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3903_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3903_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed(lean_object* v_config_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0(v_config_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v_config_3968_; lean_object* v_maxSteps_3969_; lean_object* v___x_3970_; lean_object* v_config_3971_; lean_object* v___f_3972_; lean_object* v___x_3973_; lean_object* v_target_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v_config_3968_ = lean_ctor_get(v___y_3956_, 0);
v_maxSteps_3969_ = lean_ctor_get(v_config_3968_, 1);
v___x_3970_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_3969_);
v_config_3971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_3971_, 0, v_maxSteps_3969_);
lean_ctor_set(v_config_3971_, 1, v___x_3970_);
v___f_3972_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3972_, 0, v_config_3971_);
v___x_3973_ = lean_st_ref_get(v___y_3957_);
v_target_3974_ = lean_ctor_get(v___x_3973_, 2);
lean_inc_ref(v_target_3974_);
lean_dec(v___x_3973_);
v___x_3975_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_3974_);
lean_dec_ref(v_target_3974_);
v___x_3976_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__2___redArg(v___x_3975_, v___f_3972_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1___boxed(lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass___lam__1(v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(lean_object* v_cls_3998_, lean_object* v_msg_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___redArg(v_cls_3998_, v_msg_3999_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0___boxed(lean_object* v_cls_4013_, lean_object* v_msg_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__0(v_cls_4013_, v_msg_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(lean_object* v_upperBound_4028_, lean_object* v___x_4029_, lean_object* v_config_4030_, lean_object* v_inst_4031_, lean_object* v_R_4032_, lean_object* v_a_4033_, lean_object* v_b_4034_, lean_object* v_c_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v___x_4048_; 
v___x_4048_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___redArg(v_upperBound_4028_, v___x_4029_, v_config_4030_, v_a_4033_, v_b_4034_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_4049_ = _args[0];
lean_object* v___x_4050_ = _args[1];
lean_object* v_config_4051_ = _args[2];
lean_object* v_inst_4052_ = _args[3];
lean_object* v_R_4053_ = _args[4];
lean_object* v_a_4054_ = _args[5];
lean_object* v_b_4055_ = _args[6];
lean_object* v_c_4056_ = _args[7];
lean_object* v___y_4057_ = _args[8];
lean_object* v___y_4058_ = _args[9];
lean_object* v___y_4059_ = _args[10];
lean_object* v___y_4060_ = _args[11];
lean_object* v___y_4061_ = _args[12];
lean_object* v___y_4062_ = _args[13];
lean_object* v___y_4063_ = _args[14];
lean_object* v___y_4064_ = _args[15];
lean_object* v___y_4065_ = _args[16];
lean_object* v___y_4066_ = _args[17];
lean_object* v___y_4067_ = _args[18];
lean_object* v___y_4068_ = _args[19];
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_bvAcNormalizePass_spec__1(v_upperBound_4049_, v___x_4050_, v_config_4051_, v_inst_4052_, v_R_4053_, v_a_4054_, v_b_4055_, v_c_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
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
lean_dec_ref(v___x_4050_);
lean_dec(v_upperBound_4049_);
return v_res_4069_;
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
